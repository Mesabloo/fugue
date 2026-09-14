#!/usr/bin/env bash
# Runs the LamportMutex example end to end: one name server plus three nodes (n1,
# n2, n3), all on localhost, wired together over TCP. Ctrl-C stops all of
# them.
set -euo pipefail
cd "$(dirname "$0")/../.."

bin="$(mktemp -d)"
trap 'kill $(jobs -p) 2>/dev/null; rm -rf "$bin"' EXIT

go build -o "$bin/nameserver" ./examples/lamport_mutex/nameserver
go build -o "$bin/node" ./examples/lamport_mutex

"$bin/nameserver" -bind 127.0.0.1:9000 &
sleep 0.2

"$bin/node" -name n1 -bind 127.0.0.1:9101 -ns 127.0.0.1:9000 &
"$bin/node" -name n2 -bind 127.0.0.1:9102 -ns 127.0.0.1:9000 &
"$bin/node" -name n3 -bind 127.0.0.1:9103 -ns 127.0.0.1:9000 &

wait
