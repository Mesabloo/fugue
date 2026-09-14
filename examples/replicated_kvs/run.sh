#!/usr/bin/env bash
# Runs the ReplicatedKVS example end to end: one name server, replicatedkvs.ReplicaNames'
# three replicas (r1, r2, r3), and replicatedkvs.ClientNames' two clients (c1, c2), all on
# localhost, wired together over TCP. Each client runs its Get/Put/ClockUpdate loops
# forever, so this does not exit on its own -- Ctrl-C stops all of them.
set -euo pipefail
cd "$(dirname "$0")/../.."

bin="$(mktemp -d)"
trap 'kill $(jobs -p) 2>/dev/null; rm -rf "$bin"' EXIT

go build -o "$bin/nameserver" ./examples/replicated_kvs/nameserver
go build -o "$bin/replica" ./examples/replicated_kvs/replica
go build -o "$bin/client" ./examples/replicated_kvs/client

"$bin/nameserver" -bind 127.0.0.1:9000 &
sleep 0.2

"$bin/replica" -name r1 -bind 127.0.0.1:9101 -ns 127.0.0.1:9000 &
"$bin/replica" -name r2 -bind 127.0.0.1:9102 -ns 127.0.0.1:9000 &
"$bin/replica" -name r3 -bind 127.0.0.1:9103 -ns 127.0.0.1:9000 &

"$bin/client" -name c1 -bind 127.0.0.1:9201 -ns 127.0.0.1:9000 &
"$bin/client" -name c2 -bind 127.0.0.1:9202 -ns 127.0.0.1:9000 &

wait
