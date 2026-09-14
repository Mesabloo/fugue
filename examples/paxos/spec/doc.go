// Package spec is fugue compile's output for ../Paxos.tla, kept in its own package
// (-X go-pkg:spec) so the generated file's package stays separate from ../main.go rather than
// sharing package main directly. Not checked in (see the .gitignore alongside it, since
// fugue.sh hardcodes -X go-pkg:main and so can't produce this); regenerate with:
//
//	go generate ./examples/paxos/spec
package spec

//go:generate sh -c "cd ../../.. && .lake/build/bin/fugue compile -t go -X go-pkg:spec -o examples/paxos/spec/spec.go examples/paxos/Paxos.tla"
