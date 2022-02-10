# Benchmarking for comparing traditional Dedukti encodings with adequate encodings

We benchmark the arith_fermat library in two versions: the traditional version as proposed by François Thiré[1] and the adequate version, which uses an encoding with the approach of [2].

We modified Logipedia in order to output the library in the adequate encoding in lp, using implicit arguments. Then, using the command export from lambdapi, we generated a dedukti version (also used for kontroli), in where all the implicit arguments are made explicit. 

The following are the times on my machine. Note that Dedukti does not typecheck files with dependencies without generating the object files. On the other hand, it seems that Kontroli has no option to generate object files.

|                                                  | traditional dk | adequate dk | traditional lp 2.1 | adequate lp 2.1 | traditional kontroli | adequate kontroli |
|--------------------------------------------------|----------------|-------------|--------------------|-----------------|----------------------|-------------------|
| size of .dk or .lp files                         | 1.6 MB         | 40.6 MB     | 1.7 MB             | 1.1 MB          | 1.6 MB               | 40.6 MB           |
| size of .dko or .lpo files                       | 1.4 MB         | 62.1 MB     | 18.7 MB            | 308.8 MB        |                      |                   |
| time to typecheck  (generating object files)     | 0.4 s          | 6.17 s      | 1.73 s             | 78.72 s         |                      |                   |
| time to typecheck (not  generating object files) |                |             | 1.10 s             | 75.87 s         | 0.25 s               | 3.02 s            |

When comparing both times of typechecking for Dedukti and Kontroli, we see that the adequate encoding introduces a performance loss in the order of `10^1`, which is not bad considering that we were expecting worse. The size of the .dk files grows a bit more, but in the same order of magnitude.

When comparing times for Lambdapi, we see that the performance loss is much worse. However, in fact we cannot compare these times, because the adequeta version uses implicit arguments, which need to be recalculated, whereas the traditional version has no implicit arguments. Therefore, we would need to take into account only the time used for typechecking for this comparison to be fare.

[1] Interoperability between proof systems using the logical framework Dedukti. François Thiré, PhD thesis, 2020.

[2] Adequate and computational encodings on the logical framework Dedukti, Thiago Felicissimo, draft, 2022.
