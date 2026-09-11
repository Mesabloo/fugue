---- MODULE AcceptBagsAllOperatorsGoCodegen ----
\* Expect: accepted, all the way through Go code generation. Exercises every `Bags` operator this
\* compiler gives real codegen to. `Paxos` (`Tests/examples/Paxos.tla`), the only other user, only
\* reaches `EmptyBag`/`SetToBag`/`(+)`/`CopiesIn`/`BagToSet` (the last via the `Bag(τ) <: τ -> Int`
\* coercion on a bare `DOMAIN`) -- `IsABag`/`BagIn`/`(-)`/`BagUnion`/`\sqsubseteq`/`SubBag` have no
\* coverage anywhere else reaching `.go`. `BagOfAll`/`BagCardinality` stay `E0061`-rejected on
\* purpose -- see `RejectBagCardinalityUnsupported`.

EXTENDS Bags, Naturals

CONSTANTS
    \* @type: Set(Address);
    Nodes

(*--algorithm AcceptBagsAllOperatorsGoCodegen {
    process (node \in Nodes)
        variables
            \* @type: Bag(Int);
            b1 = SetToBag({1, 2}),
            \* @type: Bag(Int);
            b2 = SetToBag({2, 3}),
            \* @type: Bool;
            isBag = FALSE,
            \* @type: Bool;
            has1 = FALSE,
            \* @type: Bag(Int);
            sum = EmptyBag,
            \* @type: Bag(Int);
            diff = EmptyBag,
            \* @type: Bag(Int);
            union = EmptyBag,
            \* @type: Bool;
            leq = FALSE,
            \* @type: Set(Bag(Int));
            subs = {},
            \* @type: Int;
            copies = 0;
    {
    p1: isBag := IsABag(b1);
        has1 := BagIn(1, b1);
        sum := b1 (+) b2;
        diff := b1 (-) b2;
        union := BagUnion({b1, b2});
        leq := b1 \sqsubseteq sum;
        subs := SubBag(b1);
        copies := CopiesIn(2, sum);
        goto Done;
    }
}*)
====
