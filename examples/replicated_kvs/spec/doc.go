// Package spec is fugue compile's output for ../ReplicatedKVS.tla, kept in its own package
// (-X go-pkg:spec) rather than package main -- see ../README.md for what this shape gives an
// integrator, this example's own two roles (replica, client) each needing their own main. Not
// checked in (see the .gitignore alongside it, since fugue.sh hardcodes -X go-pkg:main and so
// can't produce this); regenerate with:
//
//	go generate ./examples/replicated_kvs/spec
package spec

//go:generate sh -c "cd ../../.. && .lake/build/bin/fugue compile -t go -X go-pkg:spec -o examples/replicated_kvs/spec/spec.go examples/replicated_kvs/ReplicatedKVS.tla"
