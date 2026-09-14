#!/usr/bin/env bash
# Runs the PingPongs example end to end, matching PingPongs.md's "Running"
# section: one name server, one Ping, two Pongs (Pong1, Pong2), all on
# localhost, wired together over TCP. Ctrl-C stops all of them.
set -euo pipefail
cd "$(dirname "$0")/../.."

bin="$(mktemp -d)"
trap 'kill $(jobs -p) 2>/dev/null; rm -rf "$bin"' EXIT

go build -o "$bin/nameserver" ./examples/pingpong/nameserver
go build -o "$bin/ping" ./examples/pingpong/ping
go build -o "$bin/pong" ./examples/pingpong/pong

"$bin/nameserver" 127.0.0.1:9000 &
sleep 0.2

"$bin/ping" 127.0.0.1:9000 Pong1 Pong2 &
"$bin/pong" 127.0.0.1:9000 Pong1 &
"$bin/pong" 127.0.0.1:9000 Pong2 &

wait
