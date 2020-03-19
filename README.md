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
