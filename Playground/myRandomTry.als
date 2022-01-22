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
		m in m.^(hasFather+hasMother) or
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

// p1 and p2 have to be disj
pred areSiblings[p1: Person, p2: Person] {
	p1.hasMother = p2.hasMother and
	p1.hasFather = p2.hasFather
}

pred areSiblingsInLaw[p1: Person, p2: Person] {
	(p1.hasMother = p2.hasMother or
	p1.hasFather = p2.hasFather) and not areSiblings[p1, p2]
}

///

pred show {}

run show for 10 but 6 int

