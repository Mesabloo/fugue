// Package replicatedkvs is fugue compile's output for ../ReplicatedKVS.tla, as an
// importable package (-X go-pkg:replicatedkvs) rather than package main -- see
// ../../pingpong/PingPongs.md for what this shape gives an integrator, this example's own
// two roles (replica, client) each needing their own main. Not checked in (see the
// .gitignore alongside it, since fugue.sh hardcodes -X go-pkg:main and so can't produce
// this); regenerate with:
//
//	go generate ./examples/replicated_kvs/replicatedkvs
package replicatedkvs

//go:generate sh -c "cd ../../.. && .lake/build/bin/fugue compile -t go -X go-pkg:replicatedkvs -o examples/replicated_kvs/replicatedkvs/replicatedkvs.go examples/replicated_kvs/ReplicatedKVS.tla"
