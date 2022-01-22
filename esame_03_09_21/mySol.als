sig BCRdispencer {
	holdBCRs: set BCR,
}

sig BCR {
	hasBattery: BCRsBattery
}
sig BCRsBattery{
	hasStatus: BattStatus
}

abstract sig BattStatus{}
one Charged, Dead extends BattStatus{}

sig Customer{
	takenBCR: lone BCR,
	isUsualClient: lone FidelityCard,
	//scannedProducts: set Product,
	hasBill: Bill
} {#(this.takenBCR) > 0 implies #(this.isUsualClient) > 0}
// the BCR can be taken iff the client has the fidelity card

sig FidelityCard{}
sig Product{}
sig Bill{
	scannedProducts: set Product
}

// if the client has a BCR that one is not in the dispencer anymore
fact BCRatTheClientOrAtTheDispencer {
	all d: BCRdispencer, r: BCR |
		(r in d.holdBCRs) iff (r not in Customer.takenBCR)
}

fact noDeadBCRtoTheCustomer {
	all r: BCR | (r.hasBattery.hasStatus = Dead) implies (r in BCRdispencer)
}

pred getBCR[d0, d1: BCRdispencer, c0,c1: Customer, r: BCR] {
	// Pre-condition
	r in d0.holdsBCRs
	#(c0.isUsualClient) > 0 
	#(c0.takenBCR) = 0
	
	// Post-condition
	d1.holdsBCR = d0.holdsBCR - r
	c1.isUsualClient = c0.isUsualClient
	c1.takenBCR = c0.takenBCR + r
}


