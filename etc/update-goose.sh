#!/bin/bash

set -e

usage() {
  echo "Usage: $0"
  echo
  echo "Runs goose on code in go/ and outputs to src/Goose."
}

while [[ $# -gt 0 ]]; do
  case "$1" in
  -h | -help | --help)
    usage
    exit 0
    ;;
  -*)
    usage
    eDxit 1
    ;;
  *)
    break
    ;;
  esac
done

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
# run from repository root
cd "$DIR/.."

GOOSE_OUTPUT=src/Goose

if which goose 1>/dev/null 2>&1; then
  goose -out "$GOOSE_OUTPUT" -dir go ./...
else
  go run github.com/goose-lang/goose/cmd/goose@latest -out "$GOOSE_OUTPUT" -dir go ./...
fi
