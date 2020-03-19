[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

AMulet - AIG Multiplier Examination Tool
==============================================

Our tool AMulet is able to verify and certify unsigned and signed integer multipliers 
given as AIGs.

Use `./configure.sh && make` to configure and build `AMulet` and the AIGER library
in the  `aiger` sub-directory.  

Furthermore, you need to have installed <gmp> to run `AMulet`.

See [`test/README.md`](test/README.md) for testing `AMulet`.  
  

Our tool has the following usage `amulet <modus> <input.aig> <output files> [<option> ...] `.
See `amulet -h` for more detailed options.

Daniela Kaufmann
