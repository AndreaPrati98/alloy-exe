abstract sig Person {
    hasFather: lone Man,
    hasMother: lone Woman
} 
// i set them to 'lone' because otherwise would have been 
// too difficult to find the model with the analyzer

sig Man extends Person {
    hasWife: lone Woman
}
sig Woman extends Person {
    hasHusband: lone Man
}

fact oneHusbandOneWife {
    all m:Man, w:Woman | m.hasWife = w iff w.hasHusband = m
    // every man has a wife only if he is also her wife and viceversa
}

fact notOwnFather {
	no p:Person | p = p.hasFather
}

fact notOwnMother {
	no p:Person | p = p.hasMother
}

fact notMarriedWithAnchestor {
	no m: Man, w: Woman | m.hasWife in m.^(hasFather+hasMother) or
		w.hasHusband in w.^(hasFather + hasMother)
}

fact notYourOwnAnchestor {
	no m: Man, w: Woman | 
		m in m.^(hasFather+hasMother) and
		w in w.^(hasFather+hasMother) 
}

// not married if they have common anchestors
fact notMarriedWithChildOfAnchestors {
	no m: Man, w: Woman | not haveCommonAnchestor[m, w]
}

// has common anchestor
pred haveCommonAnchestor[m: Man, w: Woman] {
	m.^(hasFather + hasMother) in w.^(hasFather + hasMother)

}

///

pred show {}

run show for 10 but 6 int
