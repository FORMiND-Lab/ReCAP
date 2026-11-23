/**CFile****************************************************************

  FileName    [bmcDbmc.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based bounded model checking.]

  Synopsis    [D-BMC: Multi-property Bug Hunting.]

  Author      [Shenghu Han and YanJiang]

  Affiliation [Formind lab]

  Date        [Ver. 1.0. Started - Dec 16, 2025.]

  Revision    [$Id: bmcDbmc.c,v 1.00 2025/12/16 00:00:00 Exp $]

  Algorithm   [Algorithm 1: D-BMC (GIA Architecture)]

***********************************************************************/

#include "bmc.h"

#include "aig/gia/giaAig.h"
#include "aig/ioa/ioa.h"
#include "aig/saig/saig.h"
#include "base/main/main.h"
#include "misc/extra/extra.h"

#include <limits.h>
#include <math.h>
#ifdef ABC_USE_PTHREADS
#include <pthread.h>
#endif
ABC_NAMESPACE_IMPL_START

// 外部函数声明（saigDup.c中定义，未在头文件中声明）
extern void Saig_ManDupCones_rec(
    Aig_Man_t* p, Aig_Obj_t* pObj, Vec_Ptr_t* vLeaves, Vec_Ptr_t* vNodes, Vec_Ptr_t* vRoots);

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// D-BMC 管理器结构
extern Abc_Ntk_t* Abc_NtkFromAigPhase(Aig_Man_t* pMan);
extern Abc_Frame_t* Abc_FrameGetGlobalFrame();
extern void Gia_ManCycle(Gia_Man_t* p, Abc_Cex_t* pCex, int nFrames);
extern Gia_Man_t* Gia_ManDupFlip(Gia_Man_t* p, int* pInitState);
extern void Gia_ManCleanMark0(Gia_Man_t* p);

typedef struct Dbmc_Man_t_ Dbmc_Man_t;
typedef struct Dbmc_RelayTask_t_ Dbmc_RelayTask_t;
typedef struct Dbmc_WRec_t_ Dbmc_WRec_t;
typedef struct Dbmc_WPool_t_ Dbmc_WPool_t;
// witness pool forward decls
static Dbmc_WRec_t*
Dbmc_WRecBuild(Dbmc_Man_t* p, Abc_Cex_t* pCex, int generation, int nBaseFromAnchor);
static void Dbmc_WRecFree(Dbmc_WRec_t* w);
static int Dbmc_PoolAdmit(Dbmc_Man_t* p, Dbmc_WRec_t* w);
static int Dbmc_PoolFillRelayTask(Dbmc_Man_t* p, Dbmc_RelayTask_t* pTask);
static Abc_Cex_t* Dbmc_TruncateAnchor(Abc_Cex_t* pAnchor, int iFrame);
static void Dbmc_RelayTaskClearRound(Dbmc_RelayTask_t* pTask);
static void* Dbmc_RelayThreadRun(void* pArg);
static int Dbmc_RelayEnsureWorker(Dbmc_Man_t* p);
static void Dbmc_RelaySignalWork(Dbmc_Man_t* p);
static int Dbmc_CountMaskIntersection(word* pA, word* pB, int nWords);
static void Dbmc_EnsurePoCoiVectors(Dbmc_Man_t* p);

/* ── Witness Record + Pool definitions ─────────────────────────────────────*/
struct Dbmc_WRec_t_ {
    Abc_Cex_t* pCex; /* owned full-PI witness */
    int nDepth;      /* pCex->iFrame */
    int iSourcePo;   /* local PO index used by the similarity matrix */
    int iEntryId;    /* unique online-pool entry index j from the ReCAP algorithm */
};

struct Dbmc_WPool_t_ {
    Vec_Ptr_t* vRecs; /* all witnesses published by solved properties */
    int nCoiWords;
    int iNextEntryId;
};
struct Dbmc_Man_t_ {
    // 输入参数
    Aig_Man_t* pAig;      // 原始AIG
    Gia_Man_t* pGia;      // 状态注入需的GIA
    Saig_ParBmc_t* pPars; // BMC参数

    // PO状态跟踪
    Vec_Ptr_t* vCexes;       // 每个PO的CEX (Abc_Cex_t*)
    Vec_Int_t* vPoMap;       // 当前局部PO索引 -> 原始PO索引
    Vec_Int_t* vUnsolvedPos; // 当前未解决的PO索引列表
    Vec_Int_t* vSolvedPos;   // 全局已解决PO表: 0=未解决, 1=已解决

    // 状态注入相关
    int nBoundedLimit;   // ReCAP h: 每次状态注入后的展开上限
    int nPruneLimit;     // ReCAP rho: 从反例末帧逐拍回退的上限
    int nCandidateLimit; // ReCAP N: 每个目标最多尝试的不同反例数
    Abc_Cex_t* pLastCex; // 最新找到的完整CEX (用于relay anchor和witness拼接)
    Vec_Ptr_t* vRelayTriedEntries; // per target A_q: Vec_Int_t* of pool entry IDs

    // 统计信息
    int nSolvedPos;      // 已解决的PO数量
    int nRelaySolvedPos; // relay抢先解出的PO数量
    int nMaxGlobalFrame; // 最大全局帧数
    int nMasterFrame;    // 当前master推进帧
    int nRelayTriggered; // 已消费的候选反例次数
    abctime timeStart;   // 开始时间
    abctime timeLimit;   // 时间限制
#ifdef ABC_USE_PTHREADS
    pthread_mutex_t MutexShared; // 共享结果锁
    pthread_mutex_t MutexRelay;  // relay任务状态锁
    pthread_mutex_t MutexGia;    // protects mutable pGia marks/trav ids
    pthread_cond_t CondRelay;    // relay worker wakeup
#endif
    int fRelayRunning;            // 是否存在常驻relay worker线程
    int fRelayStop;               // 请求relay worker退出
    int fRelayWake;               // pending worker wakeup
    Dbmc_RelayTask_t* pRelayTask; // 常驻relay worker及其当前round
    Dbmc_WPool_t* pPool;
    /* Binary bit-level COI vectors and lazy pairwise intersections. */
    Vec_Int_t* vPoCoiSizes;
    Vec_Ptr_t* vPoCoiMasks;
    int fPoCoisBuilt;
    int** pPairwiseInter;
};

struct Dbmc_RelayTask_t_ {
    Dbmc_Man_t* p;
    Abc_Cex_t* pCandidateCex;
    int iEntryId;
    Vec_Int_t* vTargetPos;
    double dSimilarityMin;
    double dSimilarityMax;
#ifdef ABC_USE_PTHREADS
    pthread_t Thread;
#endif
    int fDone;
};

static __thread Dbmc_Man_t* s_pDbmcBmcCallbackMan = NULL;
static __thread Vec_Int_t* s_vDbmcBmcCallbackMap = NULL;
static __thread int s_nDbmcBmcCallbackBase = 0;
static __thread Abc_Cex_t* s_pDbmcBmcCallbackCexPrev = NULL;
static __thread Vec_Int_t* s_vDbmcBmcCallbackPiMap = NULL;
static __thread int s_nDbmcBmcCallbackPisFull = 0;
static __thread int s_nDbmcBmcCallbackRegsFull = 0;

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [创建D-BMC管理器]

  Description [初始化时立即将AIG转换为GIA]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Dbmc_Man_t* Dbmc_ManStart(Aig_Man_t* pAig, Saig_ParBmc_t* pPars, Vec_Int_t* vPoMap)
{
    Dbmc_Man_t* p;
    int i, nPos;

    p = ABC_CALLOC(Dbmc_Man_t, 1);
    p->pAig = pAig;
    p->pGia = Gia_ManFromAigSimple(pAig);

    p->pPars = pPars;

    // AIG和GIA的PO数量是一致的
    nPos = Saig_ManPoNum(pAig);
    assert(vPoMap == NULL || Vec_IntSize(vPoMap) == nPos);
    p->vCexes = Vec_PtrStart(nPos);
    p->vPoMap = vPoMap ? Vec_IntDup(vPoMap) : Vec_IntStartNatural(nPos);
    p->vUnsolvedPos = Vec_IntAlloc(nPos);
    p->vSolvedPos = Vec_IntStart(nPos);
    for (i = 0; i < nPos; i++)
        Vec_IntPush(p->vUnsolvedPos, i);

    p->nBoundedLimit = pPars->nBoundedLimit > 0 ? pPars->nBoundedLimit : 15;
    p->nPruneLimit = pPars->nDbmcPruneLimit > 0 ? pPars->nDbmcPruneLimit : 5;
    p->nCandidateLimit = pPars->nDbmcCandidateLimit > 0 ? pPars->nDbmcCandidateLimit : 5;
    p->vRelayTriedEntries = Vec_PtrStart(nPos);
    p->pPool = ABC_CALLOC(Dbmc_WPool_t, 1);
    p->pPool->vRecs = Vec_PtrAlloc(32);
    p->pPool->nCoiWords = (Gia_ManRegNum(p->pGia) + 63) / 64;
    p->pPool->iNextEntryId = 0;
    p->vPoCoiSizes = NULL;
    p->fPoCoisBuilt = 0;

#ifdef ABC_USE_PTHREADS
    pthread_mutex_init(&p->MutexShared, NULL);
    pthread_mutex_init(&p->MutexRelay, NULL);
    pthread_mutex_init(&p->MutexGia, NULL);
    pthread_cond_init(&p->CondRelay, NULL);
#endif
    p->timeStart = Abc_Clock();
    p->timeLimit = pPars->nTimeOut ? (pPars->nTimeOut * CLOCKS_PER_SEC) : 0;

    if (p->pPars->fDbmcRelayEnable)
        Dbmc_RelayEnsureWorker(p);

    return p;
}

/**Function*************************************************************

  Synopsis    [释放D-BMC管理器]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dbmc_ManStop(Dbmc_Man_t* p)
{
    Dbmc_RelayTask_t* pTask = NULL;
#ifdef ABC_USE_PTHREADS
    pthread_mutex_lock(&p->MutexRelay);
#endif
    pTask = p->pRelayTask;
    p->pRelayTask = NULL;
    p->fRelayStop = 1;
    p->fRelayWake = 1;
#ifdef ABC_USE_PTHREADS
    pthread_cond_broadcast(&p->CondRelay);
#endif
#ifdef ABC_USE_PTHREADS
    pthread_mutex_unlock(&p->MutexRelay);
#endif
    if (pTask) {
#ifdef ABC_USE_PTHREADS
        pthread_join(pTask->Thread, NULL);
#endif
        Dbmc_RelayTaskClearRound(pTask);
        ABC_FREE(pTask);
    }
    if (p->pGia)
        Gia_ManStop(p->pGia);
    if (p->pLastCex)
        Abc_CexFree(p->pLastCex);
    if (p->pPool) {
        Dbmc_WRec_t* w;
        int j;
        Vec_PtrForEachEntry(Dbmc_WRec_t*, p->pPool->vRecs, w, j) Dbmc_WRecFree(w);
        Vec_PtrFree(p->pPool->vRecs);
        ABC_FREE(p->pPool);
    }
    if (p->vPoCoiSizes)
        Vec_IntFree(p->vPoCoiSizes);
    if (p->vPoCoiMasks) {
        word* pMask;
        int j;
        Vec_PtrForEachEntry(word*, p->vPoCoiMasks, pMask, j) ABC_FREE(pMask);
        Vec_PtrFree(p->vPoCoiMasks);
    }
    if (p->pPairwiseInter) {
        int j, n = Vec_IntSize(p->vSolvedPos);
        for (j = 0; j < n; j++)
            ABC_FREE(p->pPairwiseInter[j]);
        ABC_FREE(p->pPairwiseInter);
    }
    if (p->vCexes)
        Vec_PtrFreeFree(p->vCexes);
    Vec_IntFree(p->vPoMap);
    Vec_IntFree(p->vUnsolvedPos);
    Vec_IntFree(p->vSolvedPos);
    if (p->vRelayTriedEntries) {
        Vec_Int_t* vTried;
        int j;
        Vec_PtrForEachEntry(Vec_Int_t*, p->vRelayTriedEntries, vTried, j)
            if (vTried)
                Vec_IntFree(vTried);
        Vec_PtrFree(p->vRelayTriedEntries);
    }
#ifdef ABC_USE_PTHREADS
    pthread_cond_destroy(&p->CondRelay);
    pthread_mutex_destroy(&p->MutexGia);
    pthread_mutex_destroy(&p->MutexShared);
    pthread_mutex_destroy(&p->MutexRelay);
#endif
    ABC_FREE(p);
}

/**Function*************************************************************

  Synopsis    [检查是否超时]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Dbmc_ManCheckTimeout(Dbmc_Man_t* p)
{
    if (p->timeLimit == 0)
        return 0;
    return (Abc_Clock() - p->timeStart) > p->timeLimit;
}

static inline int Dbmc_IsPoSolved(Dbmc_Man_t* p, int iPo)
{
#ifdef ABC_USE_PTHREADS
    int fSolved;
    pthread_mutex_lock(&p->MutexShared);
    fSolved = Vec_IntEntry(p->vSolvedPos, iPo) != 0;
    pthread_mutex_unlock(&p->MutexShared);
    return fSolved;
#else
    return Vec_IntEntry(p->vSolvedPos, iPo) != 0;
#endif
}

/* Caller is responsible for holding p->MutexShared (if pthreads enabled). */
static inline int Dbmc_IsPoSolvedNoLock(Dbmc_Man_t* p, int iPo)
{
    return Vec_IntEntry(p->vSolvedPos, iPo) != 0;
}

static inline int Dbmc_ManPoOrig(Dbmc_Man_t* p, int iPo)
{
    return Vec_IntEntry(p->vPoMap, iPo);
}

static inline int Dbmc_ManHasUnsolved(Dbmc_Man_t* p)
{
#ifdef ABC_USE_PTHREADS
    int fHas;
    pthread_mutex_lock(&p->MutexShared);
    fHas = p->nSolvedPos < Vec_IntSize(p->vSolvedPos);
    pthread_mutex_unlock(&p->MutexShared);
    return fHas;
#else
    return p->nSolvedPos < Vec_IntSize(p->vSolvedPos);
#endif
}

static inline int Dbmc_CommitSatResult(Dbmc_Man_t* p, int iPo, Abc_Cex_t* pCex, int nGlobalFrame)
{
    Abc_Cex_t* pCexDup;
#ifdef ABC_USE_PTHREADS
    pthread_mutex_lock(&p->MutexShared);
#endif
    if (Vec_IntEntry(p->vSolvedPos, iPo)) {
#ifdef ABC_USE_PTHREADS
        pthread_mutex_unlock(&p->MutexShared);
#endif
        return 0;
    }
    pCexDup = Abc_CexDup(pCex, -1);
    pCexDup->iPo = Dbmc_ManPoOrig(p, iPo);
    Vec_IntWriteEntry(p->vSolvedPos, iPo, 1);
    Vec_PtrWriteEntry(p->vCexes, iPo, pCexDup);
    p->nSolvedPos++;
    if (nGlobalFrame > p->nMaxGlobalFrame)
        p->nMaxGlobalFrame = nGlobalFrame;
#ifdef ABC_USE_PTHREADS
    pthread_mutex_unlock(&p->MutexShared);
#endif
    return 1;
}

static Vec_Int_t* Dbmc_ManCollectUnsolvedNoLock(Dbmc_Man_t* p)
{
    int iPo, nPos;
    Vec_Int_t* vUnsolved;
    nPos = Vec_IntSize(p->vSolvedPos);
    vUnsolved = Vec_IntAlloc(nPos);
    for (iPo = 0; iPo < nPos; iPo++)
        if (!Dbmc_IsPoSolvedNoLock(p, iPo))
            Vec_IntPush(vUnsolved, iPo);
    return vUnsolved;
}

static void Dbmc_ManRebuildUnsolved(Dbmc_Man_t* p)
{
    Vec_Int_t* vNewUnsolved;
#ifdef ABC_USE_PTHREADS
    pthread_mutex_lock(&p->MutexShared);
#endif
    vNewUnsolved = Dbmc_ManCollectUnsolvedNoLock(p);
    Vec_IntFree(p->vUnsolvedPos);
    p->vUnsolvedPos = vNewUnsolved;
#ifdef ABC_USE_PTHREADS
    pthread_mutex_unlock(&p->MutexShared);
#endif
}

static int Dbmc_PoolHasWitness(Dbmc_Man_t* p)
{
    int fHas = 0;
#ifdef ABC_USE_PTHREADS
    pthread_mutex_lock(&p->MutexShared);
#endif
    fHas = p->pPool && Vec_PtrSize(p->pPool->vRecs) > 0;
#ifdef ABC_USE_PTHREADS
    pthread_mutex_unlock(&p->MutexShared);
#endif
    return fHas;
}

static void Dbmc_ManRelayPoll(Dbmc_Man_t* p)
{
    Dbmc_RelayTask_t* pTask = NULL;
    int fDone = 0;
#ifdef ABC_USE_PTHREADS
    pthread_mutex_lock(&p->MutexRelay);
#endif
    pTask = p->pRelayTask;
    if (pTask && pTask->fDone) {
        p->pRelayTask = NULL;
        p->fRelayRunning = 0;
        fDone = 1;
    }
#ifdef ABC_USE_PTHREADS
    pthread_mutex_unlock(&p->MutexRelay);
#endif
    if (!fDone || pTask == NULL)
        return;
#ifdef ABC_USE_PTHREADS
    pthread_join(pTask->Thread, NULL);
#endif
    Dbmc_RelayTaskClearRound(pTask);
    ABC_FREE(pTask);
}

static void Dbmc_ManRelayDrain(Dbmc_Man_t* p)
{
    Dbmc_RelayTask_t* pTask = NULL;

#ifdef ABC_USE_PTHREADS
    pthread_mutex_lock(&p->MutexRelay);
#endif
    pTask = p->pRelayTask;
    p->pRelayTask = NULL;
    p->fRelayStop = 1;
    p->fRelayWake = 1;
#ifdef ABC_USE_PTHREADS
    pthread_cond_broadcast(&p->CondRelay);
#endif
#ifdef ABC_USE_PTHREADS
    pthread_mutex_unlock(&p->MutexRelay);
#endif

    if (pTask == NULL)
        return;

#ifdef ABC_USE_PTHREADS
    pthread_join(pTask->Thread, NULL);
#endif
    Dbmc_RelayTaskClearRound(pTask);
    ABC_FREE(pTask);
}

static int Dbmc_ShouldTriggerRelay(Dbmc_Man_t* p, Abc_Cex_t* pAnchor, int k)
{
    (void)k;
    if (!p->pPars->fDbmcRelayEnable)
        return 0;
    if (pAnchor == NULL)
        return 0;
    return 1;
}
/**Function*************************************************************

  Synopsis    [合并两个CEX,创建累积的完整trace]

  Description [将pCexNew追加到pCexBase后面，返回新的合并CEX。
               pCexBase可以为NULL (第一次),此时直接复制pCexNew。
               pCexNew不能为NULL。
               返回的CEX需要调用者负责释放。]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Cex_t* Dbmc_CexMerge(Abc_Cex_t* pCexBase, Abc_Cex_t* pCexNew)
{
    Abc_Cex_t* pCexMerged;
    int nPis, nRegs, nTotalFrames, i, f;
    int nBaseFrames, nNewFrames, nBaseFramesToCopy;

    if (pCexNew == NULL)
        return NULL;

    // 如果base为空，直接复制new
    if (pCexBase == NULL)
        return Abc_CexDup(pCexNew, -1);

    // 验证参数一致性
    if (pCexBase->nPis != pCexNew->nPis || pCexBase->nRegs != pCexNew->nRegs) {
        printf("Error: Cannot merge CEX with different parameters!\n");
        return NULL;
    }

    nPis = pCexNew->nPis;
    nRegs = pCexNew->nRegs;
    nBaseFrames = pCexBase->iFrame + 1; // base总共有多少帧
    nNewFrames = pCexNew->iFrame + 1;   // new有多少帧

    // 排除base的最后一帧（发生错误的帧），只复制前N-1帧
    nBaseFramesToCopy = nBaseFrames - 1;
    nTotalFrames = nBaseFramesToCopy + nNewFrames;

    // 创建合并后的CEX
    pCexMerged = Abc_CexAlloc(nRegs, nPis, nTotalFrames);
    pCexMerged->iPo = pCexNew->iPo; // 使用新的PO索引
    pCexMerged->iFrame = nTotalFrames - 1;

    // 复制寄存器初值 (来自base的初值)
    for (i = 0; i < nRegs; i++)
        if (Abc_InfoHasBit(pCexBase->pData, i))
            Abc_InfoSetBit(pCexMerged->pData, i);

    // 复制base的前N-1帧PI（排除最后一帧）
    for (f = 0; f < nBaseFramesToCopy; f++) {
        for (i = 0; i < nPis; i++) {
            if (Abc_InfoHasBit(pCexBase->pData, nRegs + nPis * f + i))
                Abc_InfoSetBit(pCexMerged->pData, nRegs + nPis * f + i);
        }
    }

    // 追加new的所有PI帧
    for (f = 0; f < nNewFrames; f++) {
        for (i = 0; i < nPis; i++) {
            if (Abc_InfoHasBit(pCexNew->pData, nRegs + nPis * f + i))
                Abc_InfoSetBit(pCexMerged->pData, nRegs + nPis * (nBaseFramesToCopy + f) + i);
        }
    }

    return pCexMerged;
}

/**Function*************************************************************

  Synopsis    [将 CEX 保存为标准 AIGER 1.9 Witness 格式 (.witness) - 扩展版]
  Description [输出格式:
               第1行: 1 (witness版本号)
               第2行: b<PO索引>
               第3行: pCex中保存的寄存器初始值
               后续行: 每帧的PI值
               最后行: .
              ]
***********************************************************************/
void Dbmc_WriteAigerWitness(Aig_Man_t* pAig, Abc_Cex_t* pCex, int iPo, char* pFileName)
{
    FILE* pFile;
    int i, f, nPis, nRegs;

    if (pAig == NULL || pCex == NULL)
        return;
    (void)pAig;

    // 获取 PI 和寄存器数量
    nPis = pCex->nPis;
    nRegs = pCex->nRegs;

    // 打开文件
    pFile = fopen(pFileName, "w");
    if (pFile == NULL) {
        printf("Error: Cannot open file %s for writing.\n", pFileName);
        return;
    }

    // 1. Header: 版本号
    fprintf(pFile, "1\n");

    // Line 2: Bad state output index
    fprintf(pFile, "b%d\n", iPo);

    // Line 3: Initial register values
    for (i = 0; i < nRegs; i++)
        fprintf(pFile, "%c", '0' + Abc_InfoHasBit(pCex->pData, i));
    fprintf(pFile, "\n");

    // Lines 4+: PI values for each frame
    // Frame f 的 PI[i] 存放在 pCex->pData 的 bit (nRegs + nPis*f + i)
    for (f = 0; f <= pCex->iFrame; f++) {
        for (i = 0; i < nPis; i++)
            fprintf(pFile, "%c", '0' + Abc_InfoHasBit(pCex->pData, nRegs + nPis * f + i));
        fprintf(pFile, "\n");
    }

    // Last line: terminator
    fprintf(pFile, ".\n");

    fclose(pFile);
}

/**Function*************************************************************

  Synopsis    [在GIA上进行有界展开检查 - BoundedCheckGia]

  Description [逻辑同 SolveSAT，但针对 GIA 进行批量检查。
               参数 pCexPrev: 前一个CEX，用于生成完整的接力witness文件]

  SideEffects []

  SeeAlso     []

***********************************************************************/
/**Function*************************************************************

  Synopsis    [COI提取 + PI映射记录]

  Description [与Saig_ManDupCones相同，但额外输出vPiMap:
               vPiMap[i] = 原始AIG中PI的CioId，对应COI-AIG的第i个PI]

***********************************************************************/
static Aig_Man_t* Dbmc_AigDupConesMapped(Aig_Man_t* pAig, int* pPos, int nPos, Vec_Int_t** pvPiMap)
{
    Aig_Man_t* pAigNew;
    Vec_Ptr_t *vLeaves, *vNodes, *vRoots;
    Aig_Obj_t* pObj;
    int i;

    vLeaves = Vec_PtrAlloc(100);
    vNodes = Vec_PtrAlloc(100);
    vRoots = Vec_PtrAlloc(100);
    for (i = 0; i < nPos; i++)
        Vec_PtrPush(vRoots, Aig_ManCo(pAig, pPos[i]));

    Aig_ManIncrementTravId(pAig);
    Aig_ObjSetTravIdCurrent(pAig, Aig_ManConst1(pAig));
    Vec_PtrForEachEntry(Aig_Obj_t*, vRoots, pObj, i)
        Saig_ManDupCones_rec(pAig, pObj, vLeaves, vNodes, vRoots);

    // 记录PI映射: COI-PI index -> 原始PI的CioId
    *pvPiMap = Vec_IntAlloc(Vec_PtrSize(vLeaves));
    Vec_PtrForEachEntry(Aig_Obj_t*, vLeaves, pObj, i) Vec_IntPush(*pvPiMap, Aig_ObjCioId(pObj));

    pAigNew = Aig_ManStart(Vec_PtrSize(vNodes));
    pAigNew->pName = Abc_UtilStrsav(pAig->pName);
    Aig_ManConst1(pAig)->pData = Aig_ManConst1(pAigNew);
    Vec_PtrForEachEntry(Aig_Obj_t*, vLeaves, pObj, i) pObj->pData = Aig_ObjCreateCi(pAigNew);
    Vec_PtrForEachEntryStart(Aig_Obj_t*, vRoots, pObj, i, nPos) Saig_ObjLiToLo(pAig, pObj)->pData =
        Aig_ObjCreateCi(pAigNew);
    Vec_PtrForEachEntry(Aig_Obj_t*, vNodes, pObj, i) pObj->pData =
        Aig_And(pAigNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj));
    Vec_PtrForEachEntry(Aig_Obj_t*, vRoots, pObj, i)
        Aig_ObjCreateCo(pAigNew, Aig_ObjChild0Copy(pObj));
    Aig_ManSetRegNum(pAigNew, Vec_PtrSize(vRoots) - nPos);

    Vec_PtrFree(vLeaves);
    Vec_PtrFree(vNodes);
    Vec_PtrFree(vRoots);
    return pAigNew;
}

/**Function*************************************************************

  Synopsis    [将COI-CEX扩展回完整PI空间]

  Description [pCexCoi是COI-AIG上的CEX，vPiMap记录COI-PI到原始PI的映射，
               nPisFull/nRegsFull是原始AIG的PI/Reg数量。
               返回完整PI空间的CEX（未映射的PI位为0）]

***********************************************************************/
static Abc_Cex_t*
Dbmc_CexExpandToFull(Abc_Cex_t* pCexCoi, Vec_Int_t* vPiMap, int nPisFull, int nRegsFull)
{
    Abc_Cex_t* pCexFull;
    int f, k, nFrames, iOrigPi;

    nFrames = pCexCoi->iFrame + 1;
    pCexFull = Abc_CexAlloc(nRegsFull, nPisFull, nFrames);
    pCexFull->iPo = pCexCoi->iPo;
    pCexFull->iFrame = pCexCoi->iFrame;

    // 复制初始寄存器值（COI-CEX的nRegs可能小于nRegsFull，多余位为0）
    for (k = 0; k < pCexCoi->nRegs && k < nRegsFull; k++)
        if (Abc_InfoHasBit(pCexCoi->pData, k))
            Abc_InfoSetBit(pCexFull->pData, k);

    // 逐帧映射PI值
    for (f = 0; f < nFrames; f++) {
        Vec_IntForEachEntry(vPiMap, iOrigPi, k)
        {
            if (Abc_InfoHasBit(pCexCoi->pData, pCexCoi->nRegs + f * pCexCoi->nPis + k))
                Abc_InfoSetBit(pCexFull->pData, nRegsFull + f * nPisFull + iOrigPi);
        }
    }
    return pCexFull;
}

static int Dbmc_ManRecordRelayCex(Dbmc_Man_t* p,
                                  int iPo,
                                  Abc_Cex_t* pCex,
                                  int nBase,
                                  Abc_Cex_t* pCexPrev,
                                  Vec_Int_t* vPiMap,
                                  int nPisFull,
                                  int nRegsFull)
{
    Abc_Cex_t *pCexExp, *pCexFull, *pCexStored;
    int iPoOrig;

    if (pCex == NULL || pCex == (Abc_Cex_t*)(ABC_PTRINT_T)1 || Dbmc_IsPoSolved(p, iPo))
        return 0;

    iPoOrig = Dbmc_ManPoOrig(p, iPo);
    pCexExp = Dbmc_CexExpandToFull(pCex, vPiMap, nPisFull, nRegsFull);
    pCexExp->iPo = iPoOrig;
    pCexFull = Dbmc_CexMerge(pCexPrev, pCexExp);
    pCexStored = pCexFull ? pCexFull : pCexExp;

    if (Dbmc_CommitSatResult(p, iPo, pCexStored, nBase + pCex->iFrame)) {
        p->nRelaySolvedPos++;
        if (!p->pPars->fSilent && p->pPars->fVerbose)
            printf("    [Relay] PO %d: SAT at local frame %d (global frame %d)  (%.2f s)\n",
                   iPoOrig,
                   pCex->iFrame,
                   nBase + pCex->iFrame,
                   (double)(Abc_Clock() - p->timeStart) / CLOCKS_PER_SEC);
        if (p->pPars->pOutFile) {
            char Buffer[1000];
            int ret;
            sprintf(Buffer, "mkdir -p %s", p->pPars->pOutFile);
            ret = system(Buffer);
            (void)ret;
            sprintf(Buffer, "%s/po%d.wit", p->pPars->pOutFile, iPoOrig);
            Dbmc_WriteAigerWitness(p->pAig, pCexStored, iPoOrig, Buffer);
        }
        /* ReCAP publishes relay-discovered witnesses back to the online pool. */
        if (pCexStored) {
            Dbmc_WRec_t* wRelay = Dbmc_WRecBuild(p, pCexStored, 1, nBase);
            if (wRelay)
                Dbmc_PoolAdmit(p, wRelay);
        }
    } else {
        iPoOrig = -1;
    }

    if (pCexFull)
        Abc_CexFree(pCexFull);
    Abc_CexFree(pCexExp);
    return iPoOrig >= 0;
}

static int Dbmc_ManBmcFailCallback(int iPoBatch, Abc_Cex_t* pCex);

static int Dbmc_ManBoundedCheckGia_RunRound(Dbmc_Man_t* p,
                                            Gia_Man_t* pGiaWork,
                                            int nLimit,
                                            int nBaseFrame,
                                            Abc_Cex_t* pCexPrev,
                                            Vec_Int_t* vTargetPos)
{
    Saig_ParBmc_t ParsBmc;
    Aig_Man_t *pTempAig, *pAigBatch;
    Vec_Int_t *vBatchPos, *vPiMap;
    abctime timeRemaining;
    int nCallTimeOut = 0;
    int i, iTargetPo, nPisFull, nRegsFull;

    pTempAig = Gia_ManToAig(pGiaWork, 0);
    nPisFull = Saig_ManPiNum(pTempAig);
    nRegsFull = Saig_ManRegNum(pTempAig);

    vBatchPos = Vec_IntAlloc(Vec_IntSize(vTargetPos));
    {
        int nPos = Saig_ManPoNum(pTempAig);
        int iStartConstrs = nPos - pTempAig->nConstrs;
        Vec_IntForEachEntry(vTargetPos, iTargetPo, i)
            if (iTargetPo >= 0 && iTargetPo < iStartConstrs && !Dbmc_IsPoSolved(p, iTargetPo))
                Vec_IntPush(vBatchPos, iTargetPo);
    }

    if (Vec_IntSize(vBatchPos) == 0 || Dbmc_ManCheckTimeout(p)) {
        Vec_IntFree(vBatchPos);
        Aig_ManStop(pTempAig);
        return 0;
    }

    // COI缩减 + 记录PI映射
    pAigBatch =
        Dbmc_AigDupConesMapped(pTempAig, Vec_IntArray(vBatchPos), Vec_IntSize(vBatchPos), &vPiMap);

    Saig_ParBmcSetDefaultParams(&ParsBmc);
    ParsBmc.nStart = 0;
    ParsBmc.nFramesMax = nLimit;
    ParsBmc.nConfLimit = p->pPars->nConfLimit;
    timeRemaining = p->timeLimit ? p->timeLimit - (Abc_Clock() - p->timeStart) : 0;
    if (p->timeLimit && timeRemaining <= 0) {
        Aig_ManStop(pAigBatch);
        Vec_IntFree(vPiMap);
        Vec_IntFree(vBatchPos);
        Aig_ManStop(pTempAig);
        return 0;
    }
    if (p->timeLimit)
        nCallTimeOut = Abc_MaxInt(1, (int)((timeRemaining + CLOCKS_PER_SEC - 1) / CLOCKS_PER_SEC));
    ParsBmc.nTimeOut = nCallTimeOut;
    ParsBmc.fSolveAll = 1;
    ParsBmc.fStoreCex = 1;
    ParsBmc.fSilent = 1;
    ParsBmc.fNotVerbose = 1;
    ParsBmc.fVerbose = 0;
    ParsBmc.fUseSatoko = p->pPars->fUseSatoko;
    ParsBmc.fUseGlucose = p->pPars->fUseGlucose;
    ParsBmc.pFuncOnFail = Dbmc_ManBmcFailCallback;

    // 设置relay回调上下文（__thread局部）
    s_pDbmcBmcCallbackMan = p;
    s_vDbmcBmcCallbackMap = vBatchPos;
    s_nDbmcBmcCallbackBase = nBaseFrame;
    s_pDbmcBmcCallbackCexPrev = pCexPrev;
    s_vDbmcBmcCallbackPiMap = vPiMap;
    s_nDbmcBmcCallbackPisFull = nPisFull;
    s_nDbmcBmcCallbackRegsFull = nRegsFull;

    Saig_ManBmcScalable(pAigBatch, &ParsBmc);

    if (pAigBatch->vSeqModelVec) {
        Abc_Cex_t* pCex;
        int iEntry;
        Vec_PtrForEachEntry(Abc_Cex_t*, pAigBatch->vSeqModelVec, pCex, iEntry)
        {
            if (pCex == NULL || pCex == (Abc_Cex_t*)(ABC_PTRINT_T)1)
                continue;
            if (iEntry >= Vec_IntSize(vBatchPos))
                continue;
            Dbmc_ManRecordRelayCex(p,
                                   Vec_IntEntry(vBatchPos, iEntry),
                                   pCex,
                                   nBaseFrame,
                                   pCexPrev,
                                   vPiMap,
                                   nPisFull,
                                   nRegsFull);
        }
    }

    s_pDbmcBmcCallbackMan = NULL;
    s_vDbmcBmcCallbackMap = NULL;
    s_vDbmcBmcCallbackPiMap = NULL;

    if (pAigBatch->vSeqModelVec) {
        Vec_PtrFreeFree(pAigBatch->vSeqModelVec);
        pAigBatch->vSeqModelVec = NULL;
    }
    Aig_ManStop(pAigBatch);
    Vec_IntFree(vPiMap);
    Vec_IntFree(vBatchPos);
    Aig_ManStop(pTempAig);

    return 1;
}

static int Dbmc_RelayTaskHasUnsolved(Dbmc_RelayTask_t* pTask)
{
    int i, iTargetPo;
    Vec_IntForEachEntry(pTask->vTargetPos, iTargetPo, i)
        if (!Dbmc_IsPoSolved(pTask->p, iTargetPo))
            return 1;
    return 0;
}

static void* Dbmc_RelayThreadRun(void* pArg)
{
    Dbmc_RelayTask_t* pTask = (Dbmc_RelayTask_t*)pArg;
    Dbmc_Man_t* p = pTask->p;
    for (;;) {
#ifdef ABC_USE_PTHREADS
        while (Dbmc_ManHasUnsolved(p) && !Dbmc_ManCheckTimeout(p) && !Dbmc_PoolHasWitness(p)) {
            pthread_mutex_lock(&p->MutexRelay);
            while (!p->fRelayStop && !p->fRelayWake && !Dbmc_ManCheckTimeout(p))
                pthread_cond_wait(&p->CondRelay, &p->MutexRelay);
            p->fRelayWake = 0;
            if (p->fRelayStop) {
                pthread_mutex_unlock(&p->MutexRelay);
                goto done;
            }
            pthread_mutex_unlock(&p->MutexRelay);
        }
#else
        if (!Dbmc_ManHasUnsolved(p) || Dbmc_ManCheckTimeout(p) || !Dbmc_PoolHasWitness(p))
            break;
#endif
        if (!Dbmc_ManHasUnsolved(p) || Dbmc_ManCheckTimeout(p))
            break;
        if (!Dbmc_PoolFillRelayTask(p, pTask))
            break;

        {
            int iBack;
            int nDepth = pTask->pCandidateCex->iFrame;
            for (iBack = 0; iBack < p->nPruneLimit && nDepth - iBack >= 0; iBack++) {
                int iFrame = nDepth - iBack;
                Abc_Cex_t* pAnchorTrunc;
                Gia_Man_t* pGiaNew;
                if (!Dbmc_RelayTaskHasUnsolved(pTask) || Dbmc_ManCheckTimeout(p))
                    break;
                pAnchorTrunc = Dbmc_TruncateAnchor(pTask->pCandidateCex, iFrame);
#ifdef ABC_USE_PTHREADS
                pthread_mutex_lock(&p->MutexGia);
#endif
                pGiaNew = Gia_ManDupCycled(p->pGia, pAnchorTrunc, iFrame);
#ifdef ABC_USE_PTHREADS
                pthread_mutex_unlock(&p->MutexGia);
#endif
                if (pGiaNew == NULL) {
                    Abc_CexFree(pAnchorTrunc);
                    continue;
                }
                if (!p->pPars->fSilent && p->pPars->fVerbose) {
                    if (p->pPars->fDbmcRandomSelect)
                        printf("    [ReCAP] targets=%d, anchor PO %d, frame %d, "
                               "back=%d/%d, selection=random, seed=%d\n",
                               Vec_IntSize(pTask->vTargetPos),
                               pTask->pCandidateCex->iPo,
                               iFrame,
                               iBack + 1,
                               Abc_MinInt(p->nPruneLimit, nDepth + 1),
                               p->pPars->nDbmcRandomSeed);
                    else
                        printf("    [ReCAP] targets=%d, anchor PO %d, frame %d, "
                               "back=%d/%d, similarity=[%.3f, %.3f]\n",
                               Vec_IntSize(pTask->vTargetPos),
                               pTask->pCandidateCex->iPo,
                               iFrame,
                               iBack + 1,
                               Abc_MinInt(p->nPruneLimit, nDepth + 1),
                               pTask->dSimilarityMin,
                               pTask->dSimilarityMax);
                }
                Dbmc_ManBoundedCheckGia_RunRound(p,
                                                 pGiaNew,
                                                 p->nBoundedLimit + 1,
                                                 iFrame,
                                                 pAnchorTrunc,
                                                 pTask->vTargetPos);
                Gia_ManStop(pGiaNew);
                Abc_CexFree(pAnchorTrunc);
            }
        }
        Dbmc_RelayTaskClearRound(pTask);
    }
done:
#ifdef ABC_USE_PTHREADS
    pthread_mutex_lock(&p->MutexRelay);
#endif
    pTask->fDone = 1;
    p->fRelayRunning = 0;
#ifdef ABC_USE_PTHREADS
    pthread_cond_broadcast(&p->CondRelay);
    pthread_mutex_unlock(&p->MutexRelay);
#endif
    return NULL;
}

static void Dbmc_RelayTaskClearRound(Dbmc_RelayTask_t* pTask)
{
    if (pTask == NULL)
        return;
    if (pTask->pCandidateCex)
        Abc_CexFree(pTask->pCandidateCex);
    if (pTask->vTargetPos)
        Vec_IntFree(pTask->vTargetPos);
    pTask->pCandidateCex = NULL;
    pTask->iEntryId = -1;
    pTask->vTargetPos = NULL;
    pTask->dSimilarityMin = 0.0;
    pTask->dSimilarityMax = 0.0;
}

static int Dbmc_RelayEnsureWorker(Dbmc_Man_t* p)
{
#ifdef ABC_USE_PTHREADS
    Dbmc_RelayTask_t* pTask;
    if (!p->pPars->fDbmcRelayEnable)
        return 0;
    pthread_mutex_lock(&p->MutexRelay);
    if (p->fRelayRunning || p->pRelayTask != NULL) {
        pthread_mutex_unlock(&p->MutexRelay);
        return 1;
    }
    p->fRelayStop = 0;
    p->fRelayWake = 0;
    pTask = ABC_CALLOC(Dbmc_RelayTask_t, 1);
    pTask->p = p;
    p->pRelayTask = pTask;
    p->fRelayRunning = 1;
    pthread_mutex_unlock(&p->MutexRelay);
    if (pthread_create(&pTask->Thread, NULL, Dbmc_RelayThreadRun, pTask) == 0)
        return 1;

    pthread_mutex_lock(&p->MutexRelay);
    p->pRelayTask = NULL;
    p->fRelayRunning = 0;
    p->fRelayStop = 1;
    p->fRelayWake = 0;
    pthread_mutex_unlock(&p->MutexRelay);
    ABC_FREE(pTask);
    return 0;
#else
    return 0;
#endif
}

static void Dbmc_RelaySignalWork(Dbmc_Man_t* p)
{
#ifdef ABC_USE_PTHREADS
    if (!p->pPars->fDbmcRelayEnable)
        return;
    Dbmc_ManRelayPoll(p);
    if (!Dbmc_RelayEnsureWorker(p))
        return;
    pthread_mutex_lock(&p->MutexRelay);
    p->fRelayWake = 1;
    pthread_cond_signal(&p->CondRelay);
    pthread_mutex_unlock(&p->MutexRelay);
#else
    (void)p;
#endif
}

/* ────────────────────────────────────────────────────────────────────────── */
/* ────────────────────────────────────────────────────────────────────────── */
/*  ReCAP online witness pool and property similarity                         */
/* ────────────────────────────────────────────────────────────────────────── */

static Dbmc_WRec_t*
Dbmc_WRecBuild(Dbmc_Man_t* p, Abc_Cex_t* pCex, int generation, int nBaseFromAnchor)
{
    Dbmc_WRec_t* w;
    int iSourcePo;
    (void)generation;
    (void)nBaseFromAnchor;
    if (pCex == NULL || pCex == (Abc_Cex_t*)(ABC_PTRINT_T)1)
        return NULL;
    if (pCex->nPis != Gia_ManPiNum(p->pGia) || pCex->nRegs != Gia_ManRegNum(p->pGia))
        return NULL;
    iSourcePo = Vec_IntFind(p->vPoMap, pCex->iPo);
    if (iSourcePo < 0)
        return NULL;
    w = ABC_CALLOC(Dbmc_WRec_t, 1);
    w->pCex = Abc_CexDup(pCex, -1);
    w->nDepth = pCex->iFrame;
    w->iSourcePo = iSourcePo;
    w->iEntryId = -1;
    return w;
}

static void Dbmc_WRecFree(Dbmc_WRec_t* w)
{
    if (w == NULL)
        return;
    if (w->pCex)
        Abc_CexFree(w->pCex);
    ABC_FREE(w);
}

/* Collect the transitive bit-level COI over register outputs.
 * A register output is part of the COI, but it is not a terminal: continue
 * through its register input so that the vector represents the sequential
 * cone instead of only the PO's immediately preceding state boundary. */
static void Dbmc_PoCoiDfs(Gia_Man_t* pGia, Gia_Obj_t* pObj, Vec_Int_t* vCoi)
{
    if (pObj == Gia_ManConst0(pGia))
        return;
    if (Gia_ObjUpdateTravIdCurrent(pGia, pObj))
        return;
    if (Gia_ObjIsAnd(pObj)) {
        Dbmc_PoCoiDfs(pGia, Gia_ObjFanin0(pObj), vCoi);
        Dbmc_PoCoiDfs(pGia, Gia_ObjFanin1(pObj), vCoi);
        return;
    }
    if (Gia_ObjIsCi(pObj) && Gia_ObjIsRo(pGia, pObj)) {
        int iLatch = Gia_ObjCioId(pObj) - Gia_ManPiNum(pGia);
        Vec_IntPush(vCoi, iLatch);
        Dbmc_PoCoiDfs(pGia, Gia_ObjFanin0(Gia_ObjRoToRi(pGia, pObj)), vCoi);
    }
}

static void Dbmc_EnsurePoCoiVectors(Dbmc_Man_t* p)
{
    Gia_Man_t* pGia;
    int nPos, i;
    if (p->fPoCoisBuilt)
        return;
#ifdef ABC_USE_PTHREADS
    pthread_mutex_lock(&p->MutexGia);
#endif
    if (p->fPoCoisBuilt) {
#ifdef ABC_USE_PTHREADS
        pthread_mutex_unlock(&p->MutexGia);
#endif
        return;
    }
    pGia = p->pGia;
    nPos = Gia_ManPoNum(pGia);
    p->vPoCoiSizes = Vec_IntStart(nPos);
    p->vPoCoiMasks = Vec_PtrStart(nPos);
    for (i = 0; i < nPos; i++) {
        Gia_Obj_t* pPo = Gia_ManPo(pGia, i);
        Vec_Int_t* vCoi = Vec_IntAlloc(16);
        word* pMask = ABC_CALLOC(word, p->pPool->nCoiWords);
        int j, iCi;
        Gia_ManIncrementTravId(pGia);
        Dbmc_PoCoiDfs(pGia, Gia_ObjFanin0(pPo), vCoi);
        Vec_IntSort(vCoi, 0);
        Vec_IntUniqify(vCoi);
        Vec_IntForEachEntry(vCoi, iCi, j)
            pMask[iCi >> 6] |= ((word)1 << (iCi & 63));
        Vec_IntWriteEntry(p->vPoCoiSizes, i, Vec_IntSize(vCoi));
        Vec_PtrWriteEntry(p->vPoCoiMasks, i, pMask);
        Vec_IntFree(vCoi);
    }
    if (nPos > 0) {
        int j, k;
        p->pPairwiseInter = ABC_CALLOC(int*, nPos);
        for (j = 0; j < nPos; j++) {
            p->pPairwiseInter[j] = ABC_ALLOC(int, nPos);
            for (k = 0; k < nPos; k++)
                p->pPairwiseInter[j][k] = -1;
        }
    }
    p->fPoCoisBuilt = 1;
#ifdef ABC_USE_PTHREADS
    pthread_mutex_unlock(&p->MutexGia);
#endif
}

static int Dbmc_CountMaskIntersection(word* pA, word* pB, int nWords)
{
    int i, count = 0;
    for (i = 0; i < nWords; i++)
        count += __builtin_popcountll((unsigned long long)(pA[i] & pB[i]));
    return count;
}

static double Dbmc_PoSimilarity(Dbmc_Man_t* p, int iSourcePo, int iTargetPo)
{
    int nSource = Vec_IntEntry(p->vPoCoiSizes, iSourcePo);
    int nTarget = Vec_IntEntry(p->vPoCoiSizes, iTargetPo);
    int nInter = p->pPairwiseInter[iSourcePo][iTargetPo];
    if (nSource == 0 || nTarget == 0)
        return nSource == nTarget ? 1.0 : 0.0;
    if (nInter < 0) {
        nInter = Dbmc_CountMaskIntersection(
            (word*)Vec_PtrEntry(p->vPoCoiMasks, iSourcePo),
            (word*)Vec_PtrEntry(p->vPoCoiMasks, iTargetPo),
            p->pPool->nCoiWords);
        p->pPairwiseInter[iSourcePo][iTargetPo] = nInter;
        p->pPairwiseInter[iTargetPo][iSourcePo] = nInter;
    }
    return (double)nInter / sqrt((double)nSource * (double)nTarget);
}

static int Dbmc_PoolAdmit(Dbmc_Man_t* p, Dbmc_WRec_t* w)
{
    if (w == NULL)
        return 0;
#ifdef ABC_USE_PTHREADS
    pthread_mutex_lock(&p->MutexShared);
#endif
    assert(w->iEntryId < 0);
    w->iEntryId = p->pPool->iNextEntryId++;
    Vec_PtrPush(p->pPool->vRecs, w);
    if (!p->pPars->fSilent && p->pPars->fVerbose)
        printf("    [ReCAP] publish entry=%d, witness PO %d, depth=%d, pool=%d\n",
               w->iEntryId, w->pCex->iPo, w->nDepth, Vec_PtrSize(p->pPool->vRecs));
#ifdef ABC_USE_PTHREADS
    pthread_mutex_unlock(&p->MutexShared);
#endif
    return 1;
}

static Vec_Int_t* Dbmc_TargetTriedEntriesNoLock(Dbmc_Man_t* p, int iTargetPo)
{
    return (Vec_Int_t*)Vec_PtrEntry(p->vRelayTriedEntries, iTargetPo);
}

static int Dbmc_TargetTriedEntryNoLock(Dbmc_Man_t* p, int iTargetPo, int iEntryId)
{
    Vec_Int_t* vTried = Dbmc_TargetTriedEntriesNoLock(p, iTargetPo);
    return vTried != NULL && Vec_IntFind(vTried, iEntryId) >= 0;
}

static int Dbmc_TargetAttemptCountNoLock(Dbmc_Man_t* p, int iTargetPo)
{
    Vec_Int_t* vTried = Dbmc_TargetTriedEntriesNoLock(p, iTargetPo);
    return vTried ? Vec_IntSize(vTried) : 0;
}

static int Dbmc_TargetMarkEntryTriedNoLock(Dbmc_Man_t* p, int iTargetPo, int iEntryId)
{
    Vec_Int_t* vTried = Dbmc_TargetTriedEntriesNoLock(p, iTargetPo);
    if (vTried == NULL) {
        vTried = Vec_IntAlloc(p->nCandidateLimit);
        Vec_PtrWriteEntry(p->vRelayTriedEntries, iTargetPo, vTried);
    }
    assert(Vec_IntFind(vTried, iEntryId) < 0);
    Vec_IntPush(vTried, iEntryId);
    return Vec_IntSize(vTried);
}

/* Assign each (target, pool-entry) pair a stable seeded pseudo-random
   priority.  Selecting the highest-priority eligible entry gives every
   target a reproducible random permutation of the online witness pool while
   preserving the normal per-target tried-entry semantics. */
static unsigned Dbmc_RandomCandidatePriority(
    int nSeed, int iTargetPo, int iEntryId)
{
    unsigned x = (unsigned)nSeed ^ 0x9e3779b9u;
    x ^= (unsigned)(iTargetPo + 1) * 0x85ebca6bu;
    x ^= (unsigned)(iEntryId + 1) * 0xc2b2ae35u;
    x ^= x >> 16;
    x *= 0x7feb352du;
    x ^= x >> 15;
    x *= 0x846ca68bu;
    x ^= x >> 16;
    return x;
}

static int Dbmc_PoolBestForTargetNoLock(Dbmc_Man_t* p, int iTargetPo, double* pSimilarity)
{
    Dbmc_WRec_t* w;
    double dBest = -1.0;
    unsigned uBest = 0;
    int i, iBest = -1;
    Vec_PtrForEachEntry(Dbmc_WRec_t*, p->pPool->vRecs, w, i)
    {
        double dSimilarity;
        if (w->iSourcePo == iTargetPo ||
            Dbmc_TargetTriedEntryNoLock(p, iTargetPo, w->iEntryId))
            continue;
        if (p->pPars->fDbmcRandomSelect) {
            unsigned uPriority = Dbmc_RandomCandidatePriority(
                p->pPars->nDbmcRandomSeed, iTargetPo, w->iEntryId);
            if (iBest < 0 || uPriority > uBest ||
                (uPriority == uBest &&
                 w->iEntryId <
                     ((Dbmc_WRec_t*)Vec_PtrEntry(p->pPool->vRecs, iBest))->iEntryId)) {
                uBest = uPriority;
                iBest = i;
            }
            continue;
        }
        dSimilarity = Dbmc_PoSimilarity(p, w->iSourcePo, iTargetPo);
        if (dSimilarity > dBest ||
            (dSimilarity == dBest &&
             (iBest < 0 ||
              w->nDepth > ((Dbmc_WRec_t*)Vec_PtrEntry(p->pPool->vRecs, iBest))->nDepth ||
              (w->nDepth == ((Dbmc_WRec_t*)Vec_PtrEntry(p->pPool->vRecs, iBest))->nDepth &&
               w->iEntryId <
                   ((Dbmc_WRec_t*)Vec_PtrEntry(p->pPool->vRecs, iBest))->iEntryId)))) {
            dBest = dSimilarity;
            iBest = i;
        }
    }
    if (pSimilarity)
        *pSimilarity = p->pPars->fDbmcRandomSelect ? -1.0 : dBest;
    return iBest;
}

/* Build a truncated copy of pAnchor with iFrame=i. */
static Abc_Cex_t* Dbmc_TruncateAnchor(Abc_Cex_t* pAnchor, int i)
{
    Abc_Cex_t* pNew;
    int b, nBits;
    int nRegs = pAnchor->nRegs;
    int nPis = pAnchor->nPis;
    pNew = Abc_CexAlloc(nRegs, nPis, i + 1);
    pNew->iPo = pAnchor->iPo;
    pNew->iFrame = i;
    nBits = nRegs + (i + 1) * nPis;
    for (b = 0; b < nBits; b++)
        if (Abc_InfoHasBit(pAnchor->pData, b))
            Abc_InfoSetBit(pNew->pData, b);
    return pNew;
}

/* For every eligible target, find its best not-yet-tried witness.  Targets
   that select the same witness are grouped into one multi-PO relay batch.
   Choosing the largest such group preserves batching without compromising
   the per-target descending-similarity candidate order. */
static int Dbmc_PoolFillRelayTask(Dbmc_Man_t* p, Dbmc_RelayTask_t* pTask)
{
    Dbmc_WRec_t* wSel;
    Vec_Int_t* vBestWitness;
    double *pBestSimilarity, *pSimilaritySums;
    int *pTargetCounts;
    int i, iBest, iTarget, nPos, nRecs, nAttempt;
    int iSelectedWitness = -1, nSelectedTargets = 0;

    if (!p->pPars->fDbmcRelayEnable)
        return 0;
    if (!p->pPars->fDbmcRandomSelect)
        Dbmc_EnsurePoCoiVectors(p);

#ifdef ABC_USE_PTHREADS
    pthread_mutex_lock(&p->MutexShared);
#endif
    nPos = Vec_IntSize(p->vSolvedPos);
    nRecs = Vec_PtrSize(p->pPool->vRecs);
    vBestWitness = Vec_IntStartFull(nPos);
    pBestSimilarity = ABC_ALLOC(double, nPos);
    pTargetCounts = ABC_CALLOC(int, nRecs);
    pSimilaritySums = ABC_CALLOC(double, nRecs);

    for (iTarget = 0; iTarget < nPos; iTarget++) {
        double dSimilarity;
        if (Dbmc_IsPoSolvedNoLock(p, iTarget) ||
            Dbmc_TargetAttemptCountNoLock(p, iTarget) >= p->nCandidateLimit)
            continue;
        iBest = Dbmc_PoolBestForTargetNoLock(p, iTarget, &dSimilarity);
        if (iBest < 0)
            continue;
        Vec_IntWriteEntry(vBestWitness, iTarget, iBest);
        pBestSimilarity[iTarget] = dSimilarity;
        pTargetCounts[iBest]++;
        pSimilaritySums[iBest] += dSimilarity;
    }

    for (i = 0; i < nRecs; i++) {
        if (pTargetCounts[i] > nSelectedTargets ||
            (pTargetCounts[i] == nSelectedTargets && pTargetCounts[i] > 0 &&
             (iSelectedWitness < 0 ||
              (!p->pPars->fDbmcRandomSelect &&
               pSimilaritySums[i] > pSimilaritySums[iSelectedWitness])))) {
            iSelectedWitness = i;
            nSelectedTargets = pTargetCounts[i];
        }
    }

    if (iSelectedWitness < 0) {
        Vec_IntFree(vBestWitness);
        ABC_FREE(pBestSimilarity);
        ABC_FREE(pTargetCounts);
        ABC_FREE(pSimilaritySums);
#ifdef ABC_USE_PTHREADS
        pthread_mutex_unlock(&p->MutexShared);
#endif
        return 0;
    }

    wSel = (Dbmc_WRec_t*)Vec_PtrEntry(p->pPool->vRecs, iSelectedWitness);
    pTask->p = p;
    pTask->pCandidateCex = Abc_CexDup(wSel->pCex, -1);
    pTask->iEntryId = wSel->iEntryId;
    pTask->vTargetPos = Vec_IntAlloc(nSelectedTargets);
    pTask->dSimilarityMin = 2.0;
    pTask->dSimilarityMax = -1.0;
    pTask->fDone = 0;

    Vec_IntForEachEntry(vBestWitness, iBest, iTarget) {
        double dSimilarity;
        if (iBest != iSelectedWitness)
            continue;
        dSimilarity = pBestSimilarity[iTarget];
        nAttempt = Dbmc_TargetMarkEntryTriedNoLock(p, iTarget, wSel->iEntryId);
        Vec_IntPush(pTask->vTargetPos, iTarget);
        pTask->dSimilarityMin = Abc_MinDouble(pTask->dSimilarityMin, dSimilarity);
        pTask->dSimilarityMax = Abc_MaxDouble(pTask->dSimilarityMax, dSimilarity);
        p->nRelayTriggered++;
        if (!p->pPars->fSilent && p->pPars->fVerbose) {
            if (p->pPars->fDbmcRandomSelect)
                printf("  >> ReCAP select: target PO %d, entry=%d, witness PO %d, "
                       "policy=random, seed=%d, attempt=%d/%d\n",
                       Dbmc_ManPoOrig(p, iTarget),
                       wSel->iEntryId,
                       pTask->pCandidateCex->iPo,
                       p->pPars->nDbmcRandomSeed,
                       nAttempt,
                       p->nCandidateLimit);
            else
                printf("  >> ReCAP select: target PO %d, entry=%d, witness PO %d, "
                       "similarity=%.3f, attempt=%d/%d\n",
                       Dbmc_ManPoOrig(p, iTarget),
                       wSel->iEntryId,
                       pTask->pCandidateCex->iPo,
                       dSimilarity,
                       nAttempt,
                       p->nCandidateLimit);
        }
    }
    if (!p->pPars->fSilent && p->pPars->fVerbose) {
        if (p->pPars->fDbmcRandomSelect)
            printf("  >> ReCAP multi-PO relay: targets=%d, entry=%d, witness PO %d, "
                   "selection=random, seed=%d\n",
                   Vec_IntSize(pTask->vTargetPos),
                   wSel->iEntryId,
                   pTask->pCandidateCex->iPo,
                   p->pPars->nDbmcRandomSeed);
        else
            printf("  >> ReCAP multi-PO relay: targets=%d, entry=%d, witness PO %d, "
                   "similarity=[%.3f, %.3f]\n",
                   Vec_IntSize(pTask->vTargetPos),
                   wSel->iEntryId,
                   pTask->pCandidateCex->iPo,
                   pTask->dSimilarityMin,
                   pTask->dSimilarityMax);
    }

    Vec_IntFree(vBestWitness);
    ABC_FREE(pBestSimilarity);
    ABC_FREE(pTargetCounts);
    ABC_FREE(pSimilaritySums);
#ifdef ABC_USE_PTHREADS
    pthread_mutex_unlock(&p->MutexShared);
#endif
    return 1;
}

/*  End ReCAP selection core                                                  */
/* ────────────────────────────────────────────────────────────────────────── */

/* Publish a committed witness, then wake the persistent ReCAP worker. */
static int
Dbmc_ManAdmitAndMaybeLaunch(Dbmc_Man_t* p, Abc_Cex_t* pAnchor, int generation, int nBaseFromAnchor)
{
    Dbmc_WRec_t* w;

    if (!Dbmc_ShouldTriggerRelay(p, pAnchor, pAnchor ? pAnchor->iFrame : 0))
        return 0;

    /* The pool retains the witness; each target records its own attempted
       entry set so the same witness can serve several target POs. */
    w = Dbmc_WRecBuild(p, pAnchor, generation, nBaseFromAnchor);
    if (w == NULL)
        return 0;
    Dbmc_PoolAdmit(p, w); /* pool takes ownership or frees it */

    /* Wake the persistent relay worker. The worker selects pool witnesses
       by itself; the master callback only admits and signals. */
#ifdef ABC_USE_PTHREADS
    Dbmc_RelaySignalWork(p);
    return 1;
#else
    {
        Dbmc_RelayTask_t* pTask = ABC_CALLOC(Dbmc_RelayTask_t, 1);
        if (!Dbmc_PoolFillRelayTask(p, pTask)) {
            ABC_FREE(pTask);
            return 0;
        }
        Dbmc_RelayThreadRun(pTask);
        Dbmc_RelayTaskClearRound(pTask);
        ABC_FREE(pTask);
        return 1;
    }
#endif
}

/**Function*************************************************************
  Synopsis    [Commit a witness produced by the master and publish it.]
***********************************************************************/
static int Dbmc_ManRecordMasterCex(Dbmc_Man_t* p, int iPo, Abc_Cex_t* pCex, int fTryRelay)
{
    int iPoOrig;

    if (pCex == NULL || pCex == (Abc_Cex_t*)(ABC_PTRINT_T)1)
        return 0;
    if (Dbmc_IsPoSolved(p, iPo))
        return 0;

    iPoOrig = Dbmc_ManPoOrig(p, iPo);
    pCex->iPo = iPoOrig;

    if (!Dbmc_CommitSatResult(p, iPo, pCex, pCex->iFrame))
        return 0;

#ifdef ABC_USE_PTHREADS
    pthread_mutex_lock(&p->MutexShared);
#endif
    if (pCex->iFrame > p->nMasterFrame)
        p->nMasterFrame = pCex->iFrame;
#ifdef ABC_USE_PTHREADS
    pthread_mutex_unlock(&p->MutexShared);
#endif

    if (p->pLastCex)
        Abc_CexFree(p->pLastCex);
    p->pLastCex = Abc_CexDup(pCex, -1);

    if (!p->pPars->fSilent && p->pPars->fVerbose)
        printf("  PO %d: SAT at frame %d  (%.2f s)\n",
               iPoOrig,
               pCex->iFrame,
               (double)(Abc_Clock() - p->timeStart) / CLOCKS_PER_SEC);

    if (p->pPars->pOutFile) {
        char Buffer[1000];
        int ret;
        sprintf(Buffer, "mkdir -p %s", p->pPars->pOutFile);
        ret = system(Buffer);
        (void)ret;
        sprintf(Buffer, "%s/po%d.wit", p->pPars->pOutFile, iPoOrig);
        Dbmc_WriteAigerWitness(p->pAig, pCex, iPoOrig, Buffer);
        if (!p->pPars->fSilent && p->pPars->fVerbose)
            printf("    Saved witness to: %s\n", Buffer);
    }

    if (fTryRelay && Dbmc_ManHasUnsolved(p))
        Dbmc_ManAdmitAndMaybeLaunch(p, p->pLastCex, 0 /* master gen */, 0 /* no anchor base */);

    return 1;
}

static int Dbmc_ManBmcFailCallback(int iPoBatch, Abc_Cex_t* pCex)
{
    Dbmc_Man_t* p = s_pDbmcBmcCallbackMan;
    int iPo;

    if (p == NULL || s_vDbmcBmcCallbackMap == NULL)
        return 0;
    if (iPoBatch < 0 || iPoBatch >= Vec_IntSize(s_vDbmcBmcCallbackMap))
        return 0;

    iPo = Vec_IntEntry(s_vDbmcBmcCallbackMap, iPoBatch);

    // Relay path: expand COI-CEX and commit immediately
    if (s_vDbmcBmcCallbackPiMap != NULL) {
        if (pCex == NULL || Dbmc_IsPoSolved(p, iPo))
            return Dbmc_ManCheckTimeout(p);

        Dbmc_ManRecordRelayCex(p,
                               iPo,
                               pCex,
                               s_nDbmcBmcCallbackBase,
                               s_pDbmcBmcCallbackCexPrev,
                               s_vDbmcBmcCallbackPiMap,
                               s_nDbmcBmcCallbackPisFull,
                               s_nDbmcBmcCallbackRegsFull);
        return Dbmc_ManCheckTimeout(p);
    }

    // Master path
    Dbmc_ManRelayPoll(p);
    Dbmc_ManRecordMasterCex(p, iPo, pCex, 1);
    return Dbmc_ManCheckTimeout(p);
}

static int Dbmc_ManSolveSATBatch(Dbmc_Man_t* p)
{
    Saig_ParBmc_t ParsBmc;
    Abc_Cex_t* pCex;
    int RetValue, iPo, nPos;

    Dbmc_ManRebuildUnsolved(p);
    if (Vec_IntSize(p->vUnsolvedPos) == 0)
        return 1;

    // 直接用p->pAig，callback通过恒等映射获取PO索引
    nPos = Saig_ManPoNum(p->pAig);
    Vec_Int_t* vPoIdentity = Vec_IntStartNatural(nPos);

    Saig_ParBmcSetDefaultParams(&ParsBmc);
    ParsBmc.nStart = p->pPars->nStart;
    ParsBmc.nFramesMax = p->pPars->nFramesMax;
    ParsBmc.nConfLimit = p->pPars->nConfLimit;
    ParsBmc.nTimeOut = p->pPars->nTimeOut;
    ParsBmc.nTimeOutOne = p->pPars->nTimeOutOne;
    ParsBmc.fSolveAll = 1;
    ParsBmc.fStoreCex = 1;
    ParsBmc.fSilent = 1;
    ParsBmc.fNotVerbose = 1;
    ParsBmc.fVerbose = 0;
    ParsBmc.fUseSatoko = p->pPars->fUseSatoko;
    ParsBmc.fUseGlucose = p->pPars->fUseGlucose;
    ParsBmc.pFuncOnFail = Dbmc_ManBmcFailCallback;

    if (!p->pPars->fSilent && p->pPars->fVerbose) {
        if (ParsBmc.nFramesMax)
            printf("\n[Master BMC3]: POs=%d, FramesMax=%d\n", nPos, ParsBmc.nFramesMax);
        else
            printf("\n[Master BMC3]: POs=%d, FramesMax=inf\n", nPos);
    }

    s_pDbmcBmcCallbackMan = p;
    s_vDbmcBmcCallbackMap = vPoIdentity;
    RetValue = Saig_ManBmcScalable(p->pAig, &ParsBmc);
    s_pDbmcBmcCallbackMan = NULL;
    s_vDbmcBmcCallbackMap = NULL;

    if (p->pAig->vSeqModelVec) {
        for (iPo = 0; iPo < nPos; iPo++) {
            pCex = (Abc_Cex_t*)Vec_PtrEntry(p->pAig->vSeqModelVec, iPo);
            if (pCex == (Abc_Cex_t*)(ABC_PTRINT_T)1)
                Vec_PtrWriteEntry(p->pAig->vSeqModelVec, iPo, NULL);
            else if (pCex != NULL)
                Dbmc_ManRecordMasterCex(p, iPo, pCex, 0);
        }
        Vec_PtrFreeFree(p->pAig->vSeqModelVec);
        p->pAig->vSeqModelVec = NULL;
    }

    p->nMasterFrame = ParsBmc.iFrame;
    Dbmc_ManRelayPoll(p);
    Dbmc_ManRebuildUnsolved(p);

    Vec_IntFree(vPoIdentity);
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [D-BMC - Algorithm 1]

  Description [GIA Architecture Implementation]

***********************************************************************/
int Saig_ManBmcScalable_Dbmc(Aig_Man_t* pAig, Saig_ParBmc_t* pPars)
{
    Dbmc_Man_t* p;
    int iPo, i;
    int RetValue = -1;
    int nTotalPo = Saig_ManPoNum(pAig);
    abctime timeStart = Abc_Clock();
    Vec_Int_t* vOutMap = Vec_IntStartNatural(nTotalPo);
    Vec_Ptr_t* vCexes = Vec_PtrStart(nTotalPo);

    /* ReCAP starts the base and relay engines directly.  The base BMC3
       engine is the only producer before its first witness; the persistent
       target-aware multi-PO relay engine starts empty and waits on the pool. */
    p = Dbmc_ManStart(pAig, pPars, vOutMap);
    p->timeStart = timeStart;

    if (!pPars->fSilent && pPars->fVerbose) {
        printf("========================================\n");
        printf("D-BMC: Multi-property Bug Hunting\n");
        printf("========================================\n");
        printf("AIG: PI=%d, PO=%d, FF=%d, AND=%d\n",
               Saig_ManPiNum(pAig),
               Saig_ManPoNum(pAig),
               Saig_ManRegNum(pAig),
               Aig_ManNodeNum(pAig));
        if (pPars->nFramesMax)
            printf("Params: MaxFrames=%d, h=%d, rho=%d, N=%d\n",
                   pPars->nFramesMax,
                   p->nBoundedLimit,
                   p->nPruneLimit,
                   p->nCandidateLimit);
        else
            printf("Params: MaxFrames=inf, h=%d, rho=%d, N=%d\n",
                   p->nBoundedLimit,
                   p->nPruneLimit,
                   p->nCandidateLimit);
        if (!pPars->fDbmcRelayEnable)
            printf("Relay engine: disabled (ablation)\n");
        else if (pPars->fDbmcRandomSelect)
            printf("Relay engine: ReCAP target-aware multi-PO, selection=random, seed=%d\n",
                   pPars->nDbmcRandomSeed);
        else
            printf("Relay engine: ReCAP target-aware multi-PO, selection=similarity\n");
        printf("========================================\n");
    }
    RetValue = Dbmc_ManSolveSATBatch(p);

    // 报告结果
    Dbmc_ManRelayPoll(p);
    Dbmc_ManRelayDrain(p);
    Dbmc_ManRebuildUnsolved(p);

    if (!pPars->fSilent) {
        int nTotalSolvedReport = p->nSolvedPos;
        printf("\n========================================\n");
        printf("D-BMC Results:\n");
        printf("  Total POs: %d\n", nTotalPo);
        printf("  Solved POs: %d (%.1f%%)\n",
               nTotalSolvedReport,
               100.0 * nTotalSolvedReport / Abc_MaxInt(1, nTotalPo));
        printf("  Unsolved POs: %d\n", nTotalPo - nTotalSolvedReport);
        printf("  Max Frame: %d\n", p->nMaxGlobalFrame);
        if (!pPars->fDbmcRelayEnable)
            printf("  Relay engine: disabled (ablation)\n");
        else if (pPars->fDbmcRandomSelect)
            printf("  Relay engine: ReCAP target-aware multi-PO "
                   "(h=%d, rho=%d, N=%d, selection=random, seed=%d)\n",
                   p->nBoundedLimit,
                   p->nPruneLimit,
                   p->nCandidateLimit,
                   pPars->nDbmcRandomSeed);
        else
            printf("  Relay engine: ReCAP target-aware multi-PO "
                   "(h=%d, rho=%d, N=%d, selection=similarity)\n",
                   p->nBoundedLimit,
                   p->nPruneLimit,
                   p->nCandidateLimit);
        printf("  Relay witness attempts: %d\n", p->nRelayTriggered);
        printf("  Relay solved POs: %d\n", p->nRelaySolvedPos);

        Abc_PrintTime(1, "  Total time", Abc_Clock() - p->timeStart);
        printf("========================================\n");
    }

    // 将 D-BMC 解决的 PO 写回原始索引的 vCexes。
    // vOutMap[j] = 原始PO索引，p->vCexes[j] = 对应CEX
    if (p->vCexes) {
        Vec_IntForEachEntry(vOutMap, iPo, i)
        {
            Abc_Cex_t* pCex = (Abc_Cex_t*)Vec_PtrEntry(p->vCexes, i);
            if (pCex) {
                Vec_PtrWriteEntry(p->vCexes, i, NULL);
                Vec_PtrWriteEntry(vCexes, iPo, pCex);
            }
        }
        Vec_PtrFreeFree(p->vCexes);
        p->vCexes = NULL;
    }

    // 设置返回值和CEX
    {
        int nTotalSolved = 0;
        Abc_Cex_t* pCex;
        Vec_PtrForEachEntry(Abc_Cex_t*, vCexes, pCex, i) if (pCex) nTotalSolved++;
        if (nTotalSolved > 0) {
            RetValue = 0;
            pAig->vSeqModelVec = vCexes;
            vCexes = NULL;
        } else if (Vec_IntSize(p->vUnsolvedPos) == 0) {
            RetValue = 1;
        } else {
            RetValue = -1;
        }
        pPars->nFailOuts = nTotalSolved;
    }

    pPars->iFrame = p->nMasterFrame;

    Dbmc_ManStop(p);
    Vec_IntFree(vOutMap);
    if (vCexes)
        Vec_PtrFreeFree(vCexes);

    return RetValue;
}

ABC_NAMESPACE_IMPL_END
