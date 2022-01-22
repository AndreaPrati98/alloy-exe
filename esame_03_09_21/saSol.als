abstract sig Boolean{}
sig True extends Boolean{}
sig False extends Boolean{}

sig Product{}
sig FidelityCard{}
sig BCR{
    isCharged: Boolean
}

sig Customer{
    card: lone FidelityCard, //se faccio disj lone FidelityCard, ogni customer ha una card diversa
    bcr: lone BCR,
    bill: set Product
}

sig Dispenser{
    d_bcr: set BCR
}

fact cards{
    no disj c1, c2: Customer | 
    #(c1.card) > 0 and
    #(c2.card) > 0 and
    c1.card = c2.card
}

fact BCR{
    no b:BCR| all c:Customer, d:Dispenser|
    b in c.bcr and
    b in d.d_bcr
}

fact FidelityCardForBCR{
    all c:Customer | #(c.bcr) > 0 => #(c.card) > 0 
}

fact BCR_charge{
    all b:BCR | b.isCharged = False => not( all c:Customer | b in c.bcr)
}

pred getBCR[d,d_up:Dispenser,c,c_up:Customer,b:BCR]{
    //Preconditions
    b.isCharged = True
    b in d.d_bcr
    #(c.card) > 0
    #(c.bcr) = 0

    //Postconditions
    d_up.d_bcr = d.d_bcr - b
    c_up.bcr = b
    c_up.card = c.card
    c_up.bill = c.bill
}

assert a1{
    no disj c1,c2: Customer |
    #(c1.card) > 0 and 
    #(c2.card) > 0 and 
    c1.card = c2.card
}

check a1 for 5 int

pred show{
    #(Customer.card) > 3
}

run show for 5 but 6 int