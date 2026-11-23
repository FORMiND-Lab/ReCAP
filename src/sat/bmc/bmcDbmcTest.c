/**CFile****************************************************************

  FileName    [bmcDbmcTest.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based bounded model checking.]

  Synopsis    [Simple test wrapper for D-BMC algorithm.]

  Author      [Shenghu Han]
  
  Affiliation [Formind lab]

  Date        [Ver. 1.0. Started - Dec 17, 2025.]

***********************************************************************/

#include "bmc.h"
#include "aig/ioa/ioa.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Simple test function to call D-BMC directly]

  Description [This is a simplified wrapper that calls Saig_ManBmcScalable_Dbmc
               directly without the complex iteration logic of bmcMulti.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Saig_ManBmcDbmcSimpleTest( Aig_Man_t * pAig, Saig_ParBmc_t * pPars )
{
    // 直接调用D-BMC算法，不添加额外的测试输出
    return Saig_ManBmcScalable_Dbmc( pAig, pPars );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
