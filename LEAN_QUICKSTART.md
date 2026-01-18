# Lean quickstart (Hyperlocal repo)

## 0. Repo root
Always run Lake commands from the repo root:
    /Users/<you>/.../hyperlocal
(where `lakefile.lean` / `lakefile.toml` lives)

Check:
    pwd
    ls lakefile.lean lakefile.toml

## 1. Fast build
    lake build Hyperlocal.Cancellation.PrimeWitness

## 2. Smoke test (recommended)
    cat > /tmp/smoke.lean <<'EOF'
    import Hyperlocal.Cancellation.PrimeWitness
    #check Hyperlocal.Cancellation.PrimeWitness.PhiShape
    #check Hyperlocal.Cancellation.PrimeWitness.finite_prime_witness_2_3
    EOF
    lake env lean /tmp/smoke.lean

## 3. Where compiled files are
Lean artifacts are here (note the extra `/lean/`):
    .lake/build/lib/lean/Hyperlocal/Cancellation/PrimeWitness.olean

Find artifacts:
    find .lake -name 'PrimeWitness.olean' -o -name 'PrimeWitness.ilean' | head

## 4. If VSCode "goes weird"
Hard reset mathlib + cache:
    rm -rf .lake/packages/mathlib
    lake update
    lake exe cache get
    lake build

