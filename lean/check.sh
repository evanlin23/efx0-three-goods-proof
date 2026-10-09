#!/usr/bin/env bash
# Build the EFX library and fail unless: no source file contains the word `sorry`; no source file
# (or lakefile.toml) uses a debug option, metaprogramming or unsafe code (tripwire below); the build
# is error-free and warning-free; every `#print axioms` certificate lists only the three standard
# axioms (or none) and the number of certificates equals the number of `#print axioms` commands in
# the sources; every declaration of the library (not only the certified ones) depends only on the
# standard axioms (CheckAxioms.lean); Lean's replay checker `leanchecker --fresh` re-checks the
# whole library, Init included, in a fresh kernel; and the project has no dependencies (core Lean
# only). The tripwire and the replay close a gap found by the formal/audit review: a declaration
# added with `set_option debug.skipKernelTC true` is never kernel-checked, yet it builds without
# warnings and `#print axioms` reports no axioms for it. Modelled on check.sh in evanlin23/mrd-efx.
set -u
cd "$(dirname "$0")"
sources=$(find EFX -name '*.lean' | sort; echo EFX.lean)
if grep -n 'sorry' $sources CheckAxioms.lean; then
  echo "CHECK FAILED: the word 'sorry' occurs in a source file"; exit 1
fi
if grep -nE 'debug\.|import[[:space:]]+Lean|run_cmd|run_meta|run_elab|addDecl|implemented_by|\bextern\b|\bunsafe\b' $sources lakefile.toml; then
  echo "CHECK FAILED: a source file uses a debug option, metaprogramming or unsafe code"; exit 1
fi
if grep -nE '^\s*require' lakefile.toml || grep -q '"name"' <(python3 -c 'import json;print(json.load(open("lake-manifest.json"))["packages"])' 2>/dev/null); then
  echo "CHECK FAILED: the project has a dependency; core Lean only"; exit 1
fi
lake build 2>&1 | tee build.log
status=${PIPESTATUS[0]}
errors=$(grep -c '^error' build.log || true)
warnings=$(grep -c '^warning' build.log || true)
sorries=$(grep -ci 'sorry' build.log || true)
axioms=$(grep -cE "' (depends on axioms: \[.*\]|does not depend on any axioms)$" build.log || true)
expected=$(cat $sources | grep -c '^#print axioms' || true)
theorems=$(cat $sources | grep -cE '^[[:space:]]*(private |protected )?theorem ' || true)
bad_axioms=$(grep 'depends on axioms' build.log | grep -v -c -E "' depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]$" || true)
echo "lake build exit=$status errors=$errors warnings=$warnings sorry-mentions=$sorries axiom-lines=$axioms expected=$expected nonstandard-axiom-lines=$bad_axioms theorems=$theorems"
if [ "$status" != "0" ] || [ "$errors" != "0" ] || [ "$warnings" != "0" ] || [ "$sorries" != "0" ] || [ "$bad_axioms" != "0" ] || [ "$axioms" != "$expected" ]; then
  echo "CHECK FAILED"; exit 1
fi
if ! lake env lean CheckAxioms.lean 2>&1 | tee -a build.log; then
  echo "CHECK FAILED: a declaration uses a non-standard axiom"; exit 1
fi
if [ "${PIPESTATUS[0]}" != "0" ]; then echo "CHECK FAILED: CheckAxioms.lean"; exit 1; fi
lake env leanchecker --fresh EFX 2>&1 | tee -a build.log
if [ "${PIPESTATUS[0]}" != "0" ]; then
  echo "CHECK FAILED: lake env leanchecker --fresh EFX rejected the library"; exit 1
fi
echo "CHECK PASSED: $axioms audited statements, $theorems theorems, standard axioms only"
