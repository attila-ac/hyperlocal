# Hyperlocal — Lean 4 Formalisation

This folder contains the Lean 4 formalisation of the core “off-zero quartet” machinery and related setup.

## Prerequisites

- **elan** (Lean toolchain manager)
- VS Code + **Lean 4** extension

> The project pins Lean to `leanprover/lean4:v4.23.0-rc2` via the `lean-toolchain` file, so you don’t need to pick a version manually.

## Quick start

```bash
# from the repo root
lake exe cache get     # fetch mathlib cache (fast)
lake build             # build everything (first time is longer)

