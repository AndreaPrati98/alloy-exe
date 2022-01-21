abstract sig Person{} 

sig Man extends Person {
    hasWife: lone Woman
}
sig Woman extends Person{
    hasHusband: lone Man
}

// fact atLeastOneManAndOneWoman {
//     #Man >= 1 and #Woman >= 1
// }

fact oneHusbandOneWife {
    all m:Man, w:Woman | m.hasWife = w iff w.hasHusband = m
}

pred show{
    // #Man > 2
    // #Woman > 2
}

run show for 5 but 6 int 