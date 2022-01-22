sig BCRdispencer {
	holdBCRs: set BCR,
}

sig BCR {
	assignedTo: lone Customer,
	hasBattery: disj BCRsBattery
}

sig BCRsBattery{
	hasStatus: BattStatus
}

abstract sig BattStatus{}
one sig Charged, Dead extends BattStatus{}

sig Customer{
	takenBCR:  disj lone BCR,
	isUsualClient: lone FidelityCard,
	hasBill: Bill
} //{#(this.takenBCR) > 0 implies #(this.isUsualClient) > 0}
// the BCR can be taken iff the client has the fidelity card

fact BCRcanBeTakenIfUsualClient {
	all c: Customer | (#(c.takenBCR) > 0) implies (#(c.isUsualClient)> 0)
}

sig FidelityCard{}
sig Product{
	cost: Int
} {cost > 0}
sig Bill{
	scannedProducts: set Product
}

fact BCRassignedToIfNotInDispencer {
	all r: BCR | #(r.assignedTo) > 0 iff r not in BCRdispencer.holdBCRs
}

// if BCR is assigned to a customer, than a customer has that BCR
fact consistencyBCRassignmentAndCustomersBCR{
	all r: BCR, c: Customer | (r in c.takenBCR) iff (c in r.assignedTo)
}

// if the client has a BCR that one is not in the dispencer anymore
fact BCRatTheClientOrAtTheDispencer {
	all d: BCRdispencer, r: BCR |
		(r in d.holdBCRs) iff (r not in Customer.takenBCR)
}

fact noDeadBCRtoTheCustomer {
	all r: BCR | (r.hasBattery.hasStatus = Dead) implies (r in BCRdispencer.holdBCRs)
}

pred getBCR[d0, d1: BCRdispencer, c0,c1: Customer, r: BCR] {
	// Pre-condition
	r in d0.holdBCRs
	#(c0.isUsualClient) > 0 
	#(c0.takenBCR) = 0
	
	// Post-condition
	d1.holdBCRs = d0.holdBCRs - r
	c1.isUsualClient = c0.isUsualClient
	c1.takenBCR = c0.takenBCR + r
}

assert noMoreThanOneCustomerPerBCR {
	no disj r0, r1: BCR | (r0.assignedTo & r1.assignedTo) != none
// r0.assignedTo = r1.assignedTo the expression on the left, here is not right, in fact it considers also the 0 = 0 as right, which is wrong!
}

check noMoreThanOneCustomerPerBCR for 10 but 6 int

pred show{}

run show for 10 but 6 int

