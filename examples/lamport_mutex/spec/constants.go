// constants.go supplies LamportMutex.tla's one free CONSTANT, Nodes -- spec.go (generated,
// not checked in, see doc.go) references it as an ordinary package-level identifier, the same
// way examples/paxos/spec/constants.go's Nodes/N/Values supply Paxos.tla's CONSTANTs there.
// Fixed here at three nodes, matching ../run.sh; changing NodeNames needs no `go generate`,
// since the generated code depends only on its name and type, not its contents.
package spec

import (
	"slices"

	"github.com/mesabloo/fugue/runtime/comm"
	"github.com/mesabloo/fugue/runtime/comm/nameserver"
	"github.com/mesabloo/fugue/runtime/tlaplus"
)

// NodeNames is Nodes spelled out as the logical names each node process registers with the
// name server under; ../main.go's -name flag picks one.
var NodeNames = []nameserver.Name{"n1", "n2", "n3"}

// Nodes is LamportMutex.tla's CONSTANT Nodes.
var Nodes = tlaplus.MkSet(comm.AddressOrd, namesToAddresses(NodeNames)...)

func namesToAddresses(names []nameserver.Name) []comm.Address {
	addrs := make([]comm.Address, len(names))
	for i, n := range names {
		addrs[i] = n
	}
	return addrs
}

// ValidNodeName reports whether name is one of NodeNames.
func ValidNodeName(name nameserver.Name) bool { return slices.Contains(NodeNames, name) }
