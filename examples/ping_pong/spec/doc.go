// Package spec is fugue compile's output for ../PingPongs.tla, kept in its own package
// (-X go-pkg:spec) rather than package main — see ../README.md. Not checked in (see the
// .gitignore alongside it, since fugue.sh hardcodes -X go-pkg:main and so can't produce this);
// regenerate with:
//
//	go generate ./examples/ping_pong/spec
package spec

//go:generate sh -c "cd ../../.. && .lake/build/bin/fugue compile -t go -X go-pkg:spec -o examples/ping_pong/spec/spec.go examples/ping_pong/PingPongs.tla"
