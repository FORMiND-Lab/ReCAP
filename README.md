# ReCAP

**Boosting multi-property hardware bug hunting with similarity-guided
counterexample relaying.**

This repository accompanies the paper *ReCAP: Boosting Multi-Property Bug
Hunting via Similarity-Guided Counterexample Relaying*. It provides the
research proof-of-concept implementation of ReCAP as an extension of
[ABC](https://github.com/berkeley-abc/abc).

ReCAP treats every counterexample as reusable reachability progress. While a
base BMC engine checks all properties, counterexamples that it discovers are
published to an online pool. A relay engine replays a selected counterexample
prefix, recovers the reachable state at the relay point, and continues a
bounded search for another property from that state. This avoids symbolically
reconstructing the same long prefix for each property.

This public PoC contains the implementation, the ABC sources needed to build
it, and the eight public HWMCC designs reported in the paper. It contains no
industrial cases or experimental result artifacts.

## How ReCAP works

For a multi-property sequential AIG with property set `Phi`, ReCAP runs two
cooperating paths:

1. **Base engine.** Incremental BMC3 searches all unsolved primary outputs
   from the legal initial state. Each discovered counterexample is committed
   immediately and inserted into a shared online pool.
2. **Similarity-guided selection.** For every unsolved target, ReCAP ranks
   source properties by the cosine similarity of their latch-level cones of
   influence (COIs). Each target maintains its own attempted-entry set, so a
   pool entry is tried at most once for that target but may serve other
   targets. Targets selecting the same entry are processed as one multi-output
   batch.
3. **Relay-state extraction.** ReCAP simulates the selected counterexample
   prefix and injects the resulting latch valuation as the initial state of a
   reduced target COI.
4. **Bounded suffix search.** BMC3 explores at most `h` local frames from the
   injected state. A successful suffix is concatenated with the retained
   prefix to produce a complete counterexample from the original legal initial
   state.
5. **Relay-point retreat.** If the suffix search fails, ReCAP moves the relay
   point backward one frame at a time, for at most `rho` points, and retries.
   Each target tries at most `N` distinct pool entries.

The base and relay paths run concurrently when pthread support is enabled.
Relay-discovered counterexamples are committed through the same callback and
are published back to the pool.

The paper combines structural and hierarchical property-name similarity. An
AIGER input does not retain hierarchical assertion names, so this PoC uses the
paper's structural fallback (`lambda = 1`):

```text
similarity(p, q) = |COI(p) intersect COI(q)|
                   / sqrt(|COI(p)| * |COI(q)|)
```

## Requirements

- Linux.
- GCC and G++ with C++17 support.
- GNU Make.
- POSIX threads.

The required ABC packages and SAT solvers are included in the source tree.
The default Make configuration does not require Readline.

## Build

```bash
make -j$(nproc)
```

This creates `./abc`. To inspect the ReCAP command-line options:

```bash
./abc -c "dbmc -h"
```

CMake is also supported. Disable the upstream unit-test target for an offline
PoC build; otherwise CMake downloads GoogleTest.

```bash
cmake -S . -B build -DABC_SKIP_TESTS=ON
cmake --build build -j
```

## Quick start

ReCAP accepts a sequential AIGER design whose primary outputs represent the
properties. Fold constraints into the properties before invoking `dbmc`, so
counterexamples in the shared pool obey the same environment assumptions.

```bash
mkdir -p witnesses
./abc -c "read design.aig; fold; dbmc -F 100 -T 300 -B 15 -P 5 -N 5 -o witnesses"
```

The run reports how many properties were solved by the base and relay paths.
With `-o`, each discovered counterexample is written as `po<index>.wit` in
AIGER 1.9 witness format.

## Paper benchmarks

The eight public multi-property HWMCC designs from Table I are under
`benchmarks/hwmcc/`.

| design | file | properties | paper: ReCAP solved (relay) |
|---|---|---:|---:|
| 6s123 | `hwmcc12__6s123.aig` | 8 | 6 (2) |
| 6s207 | `hwmcc13__6s207.aig` | 33 | 30 (20) |
| 6s250 | `hwmcc13__6s250.aig` | 1402 | 1358 (540) |
| 6s258 | `hwmcc13__6s258.aig` | 80 | 80 (37) |
| 6s259 | `hwmcc13__6s259.aig` | 244 | 16 (15) |
| 6s301 | `hwmcc13__6s301.aig` | 569 | 540 (113) |
| 6s309 | `hwmcc13__6s309.aig` | 154 | 31 (19) |
| 6s344 | `hwmcc13__6s344.aig` | 158 | 64 (13) |

The paper uses `h=35`, `rho=5`, `N=5`, structural similarity (`lambda=1`),
and a 900-second wall-clock limit. Each instance is repeated three times; the
paper reports the median solved count and average CPU-time PAR-2. For example:

```bash
./abc -c "read benchmarks/hwmcc/hwmcc12__6s123.aig; fold; dbmc -T 900 -B 35 -P 5 -N 5"
```

A short smoke test can use a smaller global limit. It checks the executable
and relay path, but is not a reproduction of the three-run paper result:

```bash
./abc -c "read benchmarks/hwmcc/hwmcc12__6s123.aig; fold; dbmc -T 30 -B 35 -P 5 -N 5"
```

On the reference build, this smoke test found 6 of 8 counterexamples, with 2
found by the relay path. This matches the `6 (2)` solved-count decomposition
in Table I; the shortened single run does not reproduce the paper's CPU-time
PAR-2 statistic.

## ReCAP options

```text
dbmc [-SFTHGCBPNK num] [-Lo path] [-QRsgvzh]
```

| option | meaning | default |
|---|---|---:|
| `-F n` | maximum number of base-engine frames; `0` means unlimited | `0` |
| `-T s` | global runtime limit in seconds; `0` means unlimited | `0` |
| `-B n` | relay upper bound `h` | `15` |
| `-P n` | prune upper bound `rho` | `5` |
| `-N n` | candidate limit | `5` |
| `-o dir` | directory for AIGER witness files | disabled |
| `-R` | disable the relay path, leaving the base engine only | relay enabled |
| `-Q` | use seeded-random selection instead of COI similarity | similarity |
| `-K n` | seed used by `-Q` | `1` |
| `-v` | toggle verbose output | enabled |

The inherited BMC3 controls `-S`, `-H`, `-G`, `-C`, `-L`, `-s`, `-g`, and
`-z` remain available; run `dbmc -h` for their current descriptions.

## Implementation map

| path | role |
|---|---|
| `src/sat/bmc/bmcDbmc.c` | online witness pool, COI similarity, candidate batching, state relaying, retreat, callbacks, and witness reconstruction |
| `src/sat/bmc/bmcBmc3.c` | BMC3 defaults and callback support used by ReCAP |
| `src/sat/bmc/bmc.h` | ReCAP parameters added to `Saig_ParBmc_t` |
| `src/base/abci/abc.c` | registration and parsing of the `dbmc` command |
| `src/aig/gia/giaDup.c` | GIA state injection used to start a relay search from a reachable state |
| `src/sat/bmc/module.make` | inclusion of the ReCAP implementation in the ABC build |

The remaining `src/` tree is the ABC codebase on which the PoC is built.

## Scope and limitations

- Property-name similarity from the paper is unavailable for plain AIGER
  inputs because hierarchy and assertion names have already been erased.

## Repository layout

```text
src/             ABC plus the ReCAP implementation
test/            upstream ABC unit-test scaffolding
benchmarks/hwmcc/ the eight public designs from Table I
Makefile         primary build
CMakeLists.txt   optional CMake build
abc.rc           default ABC command aliases
copyright.txt    ABC license and copyright notice
```

## Citation

To be updated after DATE 2027.

## License

This implementation is distributed with the ABC source tree and its
permissive license; see [`copyright.txt`](copyright.txt). ReCAP-specific files
retain the notices present in their source headers.
