# Covering-radius-via-clubs

## Purpose

This repository contains standalone Magma scripts for computing the covering radius of selected families of one-dimensional rank-metric codes considered in the accompanying paper.

The computations use the mathematical criteria and the lower and upper bounds proved or recalled in the paper to determine the exact covering radius. Mathematical details and implementation notes are provided in the internal documentation of each script and in the paper.

## Scripts

All computations use extension degree $m=6$, including the cases with length $n=5$ or $n=7$. The filename `check_cr_nkd_qx.m` records the length $n$, dimension $k$, minimum rank distance $d$, and base-field order $q=x$.

|             Script             |    Parameters     |                        Purpose                               |
|--------------------------------|------------------ |--------------------------------------------------------------|
| `check_cr_513_q2.m`            | $[5,1,3]_{2^6/2}$ | Exhaustive classification of the relevant generator classes. |
| `check_cr_513_q3.m`            | $[5,1,3]_{3^6/3}$ | Exhaustive classification of the relevant generator classes. |
| `check_cr_613_q2.m`            | $[6,1,3]_{2^6/2}$ | Exhaustive classification of the relevant generator classes. |
| `check_cr_613_q3.m`            | $[6,1,3]_{3^6/3}$ | Exhaustive classification of the relevant generator classes. |
| `check_cr_613_q3_single.m`     | $[6,1,3]_{3^6/3}$ | Test of one prescribed ordered generator.                    |
| `check_cr_614_q2.m`            | $[6,1,4]_{2^6/2}$ | Exhaustive classification of the relevant generator classes. |
| `check_cr_614_q3.m`            | $[6,1,4]_{3^6/3}$ | Exhaustive classification of the relevant generator classes. |
| `check_cr_714_q2.m`            | $[7,1,4]_{2^6/2}$ | Exhaustive classification of the relevant generator classes. |
| `check_cr_714_q3.m`            | $[7,1,4]_{3^6/3}$ | Exhaustive classification of the relevant generator classes. |

The suffix `_single` distinguishes the single-generator implementation from the exhaustive script with the same parameters.

## Running the scripts

Magma is required. Each script is standalone and should be run in a separate Magma session.

If necessary, edit the configuration assignments in the file before loading it. These include the batch limits `StartRep` and `EndRep`, early-stop options, output and progress controls, internal checks, and `AutoRun`. In the single-generator script, edit `GeneratorFirstThree` to select the generator. The ternary $[6,1,3]$ exhaustive script also provides `ExamplesOnly`.

A complete classification requires processing all representatives without enabling an early-stop option.
