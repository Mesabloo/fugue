package fixture

import "github.com/mesabloo/fugue/runtime/comm"

// intAddress is a minimal integrator-supplied comm.Address, standing in for the
// real thing (a socket path, a host and port, ...) — comm.Address is
// deliberately left unspecified by the runtime, mirroring
// runtime/comm/address_test.go's own stand-in, which a Go test file cannot
// export for another package to reuse.
type intAddress int

func (a intAddress) Eq(other comm.Address) bool { return a == other.(intAddress) }
func (a intAddress) Lt(other comm.Address) bool { return a < other.(intAddress) }

// PID is the fixture's own CONSTANT: the one process's identity.
var PID = comm.Address(intAddress(1))
