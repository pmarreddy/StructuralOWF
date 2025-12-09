#!/bin/bash
set -e
echo "Building Lean formalization..."
cd lean && lake build
echo "✓ Build complete"
