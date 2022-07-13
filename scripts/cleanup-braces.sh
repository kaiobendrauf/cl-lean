#!/usr/bin/env bash

set -exo pipefail

find src -name '*.lean' | xargs ./scripts/cleanup-braces.py
