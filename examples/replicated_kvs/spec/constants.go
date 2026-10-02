// constants.go supplies ReplicatedKVS.tla's two free CONSTANTs, ReplicaSet and ClientSet --
// spec.go (generated, not checked in, see doc.go) references them as ordinary
// package-level identifiers, the same way examples/paxos/spec/constants.go's Nodes/N/Values
// supply Paxos.tla's CONSTANTs there. Fixed here at three replicas and two clients, matching
// ../run.sh; changing these values needs no `go generate`, since the generated code depends
// only on their names and types, not their contents.
package spec

import (
	"slices"

	"github.com/mesabloo/fugue/runtime/comm"
	"github.com/mesabloo/fugue/runtime/comm/nameserver"
	"github.com/mesabloo/fugue/runtime/tlaplus"
)

// ReplicaNames and ClientNames are ReplicaSet/ClientSet spelled out as the logical names each
// replica/client process registers with the name server under; replica/main.go's and
// client/main.go's -name flag picks one.
var ReplicaNames = []nameserver.Name{"r1", "r2", "r3"}
var ClientNames = []nameserver.Name{"c1", "c2"}

// ReplicaSet is ReplicatedKVS.tla's CONSTANT ReplicaSet.
var ReplicaSet = tlaplus.MkSet(comm.AddressOrd, namesToAddresses(ReplicaNames)...)

// ClientSet is ReplicatedKVS.tla's CONSTANT ClientSet.
var ClientSet = tlaplus.MkSet(comm.AddressOrd, namesToAddresses(ClientNames)...)

// MaxClock is ReplicatedKVS.tla's CONSTANT MaxClock, the upper bound on a client's
// Lamport clock before it disconnects.
var MaxClock tlaplus.Int = tlaplus.MkInt(100)

func namesToAddresses(names []nameserver.Name) []comm.Address {
	addrs := make([]comm.Address, len(names))
	for i, n := range names {
		addrs[i] = n
	}
	return addrs
}

// ValidReplicaName reports whether name is one of ReplicaNames.
func ValidReplicaName(name nameserver.Name) bool { return slices.Contains(ReplicaNames, name) }

// ValidClientName reports whether name is one of ClientNames.
func ValidClientName(name nameserver.Name) bool { return slices.Contains(ClientNames, name) }
