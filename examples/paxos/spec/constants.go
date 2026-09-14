// constants.go supplies Paxos.tla's free CONSTANTs -- spec.go (generated, not checked in, see
// doc.go) references them as ordinary package-level identifiers, the same way
// examples/replicated_kvs/spec/constants.go's ReplicaSet/ClientSet supply
// ReplicatedKVS.tla's CONSTANTs there. Fixed here at three nodes and three proposable
// values, matching ../run.sh; changing these values needs no `go generate`, since the
// generated code depends only on their names and types, not their contents.
package spec

import (
	"slices"

	"github.com/mesabloo/fugue/runtime/comm"
	"github.com/mesabloo/fugue/runtime/comm/tcp"
	"github.com/mesabloo/fugue/runtime/tlaplus"
)

// NodeNames is Nodes spelled out as the logical names (comm/tcp.Name values) each node
// process registers with the name server under; ../main.go's -name flag picks one.
var NodeNames = []string{"n1", "n2", "n3"}

// N is Paxos.tla's CONSTANT N.
var N tlaplus.Int = tlaplus.MkInt(len(NodeNames))

// Values is Paxos.tla's CONSTANT Values: the pool a leader's CHOOSE picks a
// proposal from once it has a quorum of "1b" replies carrying no value.
var Values = tlaplus.MkSet(tlaplus.StrOrd, tlaplus.Str("red"), tlaplus.Str("green"), tlaplus.Str("blue"))

// Nodes is Paxos.tla's CONSTANT Nodes. It holds logical identities
// (comm/tcp.Name values), kept apart from the "host:port" each process
// actually binds to — the name server bridges the two at Register/Lookup
// time, not here, so this can be built once at package init.
var Nodes = tlaplus.MkSet(comm.AddressOrd, namesToAddresses(NodeNames)...)

// MaxRound is Paxos.tla's CONSTANT MaxRound, the upper bound on ballot round numbers.
var MaxRound tlaplus.Int = tlaplus.MkInt(1000)

func namesToAddresses(names []string) []comm.Address {
	addrs := make([]comm.Address, len(names))
	for i, n := range names {
		addrs[i] = tcp.Name(n)
	}
	return addrs
}

// ValidNodeName reports whether name is one of NodeNames.
func ValidNodeName(name string) bool { return slices.Contains(NodeNames, name) }
