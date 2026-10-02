// Package tcp is a concrete implementation of the comm endpoints over TCP: a
// process reaches its peers across the network rather than over Go channels in
// one address space.
//
// The comm package deliberately ships only interfaces, leaving the medium to
// whoever builds a runnable system out of generated code. This package is one
// such choice, kept in the tree because a runnable distributed example needs
// endpoints that actually cross a machine boundary, and a hand-written pair per
// example is worse than one shared, tested implementation.
//
// The pieces fit together as follows. Each process opens a Listen endpoint for
// its own mailbox and registers the address it bound to with the name server of
// package nameserver under a stable logical name. A process that needs to send
// to a peer looks that peer's name up, learns a host and port, and opens a Dial
// endpoint to it. Values on the wire are gob-encoded, so a concrete type that
// travels in an interface-typed field — an address in a comm.Address field, say
// — must be registered with gob by whoever defines it.
//
// Nothing here attempts fault tolerance beyond reconnection: the source
// language has no vocabulary for a peer that has permanently failed, so a
// broken connection is treated as one that has not come up yet.
package tcp
