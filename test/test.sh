#!/bin/sh


# Verifying a simple unsigned multiplier
echo "substitution" > btor64.log
../amulet -substitute btor64.aig btor64.cnf btor64_rewr.aig >> btor64.log
echo "verify" >> btor64.log
../amulet -verify btor64_rewr.aig  >> btor64.log

# Verifying a faulty unsigned multiplier
echo "substitution" > btor2faulty.log
../amulet -substitute btor2faulty.aig btor2faulty.cnf btor2faulty_rewr.aig >> btor2faulty.log
echo "verify" >> btor2faulty.log
../amulet -verify btor2faulty_rewr.aig  >> btor2faulty.log

# Verifying a complex unsigned multiplier
echo "substitution" > bpwtcl64.log
../amulet -substitute bpwtcl64.aig bpwtcl64.cnf bpwtcl64_rewr.aig >> bpwtcl64.log
echo "verify" >> bpwtcl64.log
../amulet -verify bpwtcl64_rewr.aig  >> bpwtcl64.log

# Certifying a complex signed multiplier
echo "substitution" > s_sparcl64.log
../amulet -substitute s_sparcl64.aig s_sparcl64.cnf s_sparcl64_rewr.aig -signed >> s_sparcl64.log
echo "certify" >> s_sparcl64.log
../amulet -certify -signed s_sparcl64_rewr.aig s_sparcl64.polys s_sparcl64.pac s_sparcl64.spec >> s_sparcl64.log
