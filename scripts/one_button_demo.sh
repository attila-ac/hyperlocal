#!/usr/bin/env bash
set -euo pipefail

echo "==> Building umbrella (paper order)…"
lake build Hyperlocal.Manuscript

echo "==> Running smoke checks…"
lake build Hyperlocal.Smoke

echo "✅ One-button demo completed successfully."

