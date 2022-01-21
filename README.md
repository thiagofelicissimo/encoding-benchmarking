# Benchmarking for comparing traditional Dedukti encodings with adequate encodings

We benchmark the arith_fermat library in two versions: the traditional version as proposed by François Thiré and the adequate version, which uses the principles from my draft.

The following are the times on my machine. Note that Dedukti does not typecheck files with dependencies without generating the object files. On the other hand, it seems that Kontroli has no option to generate object files.

|                                                  | traditional dk | adequate dk | traditional lp 2.1 | adequate lp 2.1 | traditional kontroli | adequate kontroli |
|--------------------------------------------------|----------------|-------------|--------------------|-----------------|----------------------|-------------------|
| size of .dk or .lp files                         | 1.6 MB         | 26.8 MB     | 1.7 MB             | 1.4 MB          | 1.6 MB               | 26.8 MB           |
| size of .dko or .lpo files                       | 1.4 MB         | 51.1 MB     | 18.7 MB            | 367.4 MB        |                      |                   |
| time to typecheck  (generating object files)     | 0.39 s         | 6.5 s       | 1.67 s             | 88.9 s          |                      |                   |
| time to typecheck (not  generating object files) |                |             | 1.05 s             | 86.55 s         | 0.24 s               | 3.78 s            |

We modified Logipedia in order to output the library in the adequate encoding in lp, using implicit arguments --- this is why the library in the adequate lp version has a comparable size to the one of the traditional version. Then, using the command export from lambdapi, we generated a dedukti version, in where all the implicit arguments are made explicit. We note that, due to a problem with Lambdapi, three of the proofs in the file nat had to be axiomatized. However, their size is negligible when compared with the rest of the library, so this does not affect our comparison. 

When comparing both times of typechecking for Dedukti and Kontroli, we see that the adequate encoding introduces a performance loss in the order of `10^1`, which is not bad. The size of the .dk files also grows in the same order of magnitude. 

When comparing times for Lambdapi, we see that the performance loss is much worse, almost in the order of `10^2`. This is probably due to the fact that, as the adequate lp version uses implicit arguments, those need to be computed, whereas this functionality is not used in the traditional version. Therefore, there is a tradeoff when deciding if a library should be stored in .lp or .dk : .dk takes much less time to typecheck, but are bigger, whereas .lp files are very small, but take very long to typecheck. Given the performance loss, the first option is probably better.



