package nameserver

import (
	"encoding/gob"

	"github.com/mesabloo/fugue/runtime/comm"
)

// Name is a process identity that is nothing but its logical name.
//
// The name server maps a Name to the host and port the process is currently
// reachable at, so generated code compares and routes on the stable name while
// the transport deals in addresses that change from run to run. self is a Name,
// the keys of a Network's indexed channel are Names, and the from field a Pong
// puts in its message is a Name.
//
// Eq and Lt are the comm.Address contract. The order is lexicographic on the
// name, which is the arbitrary-but-total choice the interface documents as the
// integrator's: it makes CHOOSE over a set of addresses resolve to the
// alphabetically first name. Both methods assume the other address is also a
// Name — every address in one running system comes from this package — and
// panic otherwise, the same stance comm's own tests take.
type Name string

// Eq reports whether two identities are the same name.
func (n Name) Eq(other comm.Address) bool { return n == other.(Name) }

// Lt orders identities lexicographically by name.
func (n Name) Lt(other comm.Address) bool { return n < other.(Name) }

func init() {
	// A message field typed as comm.Address travels as an interface value, and
	// gob refuses to encode or decode a concrete type behind an interface unless
	// it has been registered. Every process registers itself through this
	// package, so this runs at both ends of every connection.
	gob.Register(Name(""))
}
