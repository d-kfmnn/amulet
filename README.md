[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

AMulet - AIG Multiplier Examination Tool
==============================================

Our tool AMulet is able to verify and certify unsigned and signed integer multipliers 
given as AIGs.

Use `./build.sh` to configure and build `AMulet` and the AIGER library in the  `aiger` sub-directory.  

Furthermore, you need to have installed `gmp` to run `AMulet`.

See [`test/README.md`](test/README.md) for testing `AMulet`.  
  

Our tool has the following usage `amulet <modus> <input.aig> <output files> [<option> ...] `.
See `amulet -h` for more detailed options.

For further information we refer to the papers:

Daniela Kaufmann, Armin Biere, Manuel Kauers. 
 [`Verifying Large Multipliers by Combining SAT and Computer Algebra.`](http://fmv.jku.at/papers/KaufmannBiereKauers-FMCAD19.pdf)
In Proc. 19th Intl. Conf. on Formal Methods in Computer Aided Design (FMCAD'19), pages 28-36, IEEE 2019.

and 

Daniela Kaufmann, Armin Biere, Manuel Kauers. 
 [`SAT, Computer Algebra, Multipliers.`](http://fmv.jku.at/papers/KaufmannBiereKauers-Vampire19.pdf)
In Vampire 2018 and Vampire 2019. The 5th and 6th Vampire Workshops, pages 1-18, EasyChair 2020.



Daniela Kaufmann

------------------------------------------------------------------------------------------------------
20.07.2020 AMulet Version 5:
Improved: 
  - Final stage-adder detection for multipliers containing redundant binary addition trees. 

16.06.2020 AMulet Version 4:
Fixed:
  - Fixed bugs in adder substitution for signed multipliers.

02.06.2020 AMulet Version 3:
Added features:
  - Option '-nss': to generate Nullstellensatz proofs instead of PAC proofs

11.05.2020 AMulet Version 2:
Added features:
  - Counter examples are generated whenever the final remainder is not 0.
  - Option '-swap' swaps input bitvectors a,b and uses alternative names for internal variables. 
  - Option '-expanded-pac' can be used to generate PAC proofs, where antecedents are extended. 
  - Option '-print_idx <int>' allows to manually set the start of the index counter for PAC proofs.

19.03.2020 AMulet Version 1:
Initial commit.




