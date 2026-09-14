#!/usr/bin/env bash
# Runs the PingPongs example end to end, matching README.md's "Run"
# section: one name server, one Ping, two Pongs (Pong1, Pong2), all on
# localhost, wired together over TCP. Ctrl-C stops all of them.
set -euo pipefail
cd "$(dirname "$0")/../.."

bin="$(mktemp -d)"
trap 'kill $(jobs -p) 2>/dev/null; rm -rf "$bin"' EXIT

go build -o "$bin/nameserver" ./examples/ping_pong/nameserver
go build -o "$bin/ping" ./examples/ping_pong/ping
go build -o "$bin/pong" ./examples/ping_pong/pong

"$bin/nameserver" 127.0.0.1:9000 &
sleep 0.2

"$bin/ping" 127.0.0.1:9000 Pong1 Pong2 &
"$bin/pong" 127.0.0.1:9000 Pong1 &
"$bin/pong" 127.0.0.1:9000 Pong2 &

wait
