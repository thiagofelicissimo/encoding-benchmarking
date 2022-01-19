# Benchmarking for comparing traditional Dedukti encodings with adequate encodings

We benchmark the arith_fermat library in two versions: the traditional version as proposed by François Thiré and the adequate version, which uses the principles from my draft.

The following are the times on my machine.


|                            | traditional dk | adequate dk | adequate lp |
|----------------------------|----------------|-------------|-------------|
| size of .dk or .lp files   | 1.6 MB         | 26.8 MB     | 1.4 MB      |
| size of .dko or .lpo files | 1.4 MB         | 51.1 MB     | 367.4 MB    |
| time to typecheck          | 0.4 s          | 6.45 s      | 88.9 s      |

We modified Logipedia in order to output the library in the adequate encoding in lp, using implicit arguments --- this is why the library in the adequate lp version has a comparable size to the one of the traditional version. Then, using the command export from lambdapi, we generated a dedukti version, in where all the implicit arguments are made explicit.

When comparing both times of typechecking for Dedukti, we see that the adequate encoding introduces a performance loss in the order of `10^1`, which is not bad. The size of the .dk files also grows in the same order of magnitude. When comparing the traditional dk version with the adequate lp version, we see that performance loss is much worse. However, as the comparison is across different typecheckers, it is not a fair one.
