abstract sig Person{
    hasFather: Man,
    hasMother: Woman
}

sig Man extends Person {
    hasWife: lone Woman
}
sig Woman extends Person{
    hasHusband: lone Man
}

fact oneHusbandOneWife {
    all m:Man, w:Woman | m.hasWife = w iff w.hasHusband = m
    // every man has a wife only if he is also her wife and viceversa
}

fact notOwnParent {
	no p:Person | p in p.hasFather or p in p.hasMother
}

pred show{}

run show for 5
