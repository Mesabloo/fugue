// Package pingpong is fugue compile's output for ../PingPongs.tla, as an
// importable package (-X go-pkg:pingpong) rather than package main — see
// ../PingPongs.md. Not checked in (see the .gitignore alongside it, since
// fugue.sh hardcodes -X go-pkg:main and so can't produce this); regenerate
// with:
//
//	go generate ./examples/pingpong/pingpong
package pingpong

//go:generate sh -c "cd ../../.. && .lake/build/bin/fugue compile -t go -X go-pkg:pingpong -o examples/pingpong/pingpong/pingpong.go examples/pingpong/PingPongs.tla"
