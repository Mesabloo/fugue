// constants.go supplies ReplicatedKVS.tla's two free CONSTANTs, ReplicaSet and ClientSet --
// replicatedkvs.go (generated, not checked in, see doc.go) references them as ordinary
// package-level identifiers, the same way examples/paxos/main.go's Nodes/N/Values supply
// Paxos.tla's CONSTANTs there. Fixed here at three replicas and two clients, matching
// ../run.sh; changing these values needs no `go generate`, since the generated code depends
// only on their names and types, not their contents.
package replicatedkvs

import (
	"slices"

	"github.com/mesabloo/fugue/runtime/comm"
	"github.com/mesabloo/fugue/runtime/comm/tcp"
	"github.com/mesabloo/fugue/runtime/tlaplus"
)

// ReplicaNames and ClientNames are ReplicaSet/ClientSet spelled out as the logical names
// (comm/tcp.Name values) each replica/client process registers with the name server under;
// replica/main.go's and client/main.go's -name flag picks one.
var ReplicaNames = []string{"r1", "r2", "r3"}
var ClientNames = []string{"c1", "c2"}

// ReplicaSet is ReplicatedKVS.tla's CONSTANT ReplicaSet.
var ReplicaSet = tlaplus.MkSet(comm.AddressOrd, namesToAddresses(ReplicaNames)...)

// ClientSet is ReplicatedKVS.tla's CONSTANT ClientSet.
var ClientSet = tlaplus.MkSet(comm.AddressOrd, namesToAddresses(ClientNames)...)

func namesToAddresses(names []string) []comm.Address {
	addrs := make([]comm.Address, len(names))
	for i, n := range names {
		addrs[i] = tcp.Name(n)
	}
	return addrs
}

// ValidReplicaName reports whether name is one of ReplicaNames.
func ValidReplicaName(name string) bool { return slices.Contains(ReplicaNames, name) }

// ValidClientName reports whether name is one of ClientNames.
func ValidClientName(name string) bool { return slices.Contains(ClientNames, name) }
