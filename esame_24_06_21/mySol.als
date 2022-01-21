abstract sig PackSize{}
one sig Small, Large extends PackSize{}
sig Package{
    size: PackSize
}

sig TruckSize{}
sig Truck{
    size: TruckSize
}

// Define a signature TruckStatus that represents the snapshot of a truck, that is, the truck with its current
// content and current driver. Ensure that the following constraint holds: a truck never exceeds its maximum
// capacity, which corresponds to an amount of packages whose size is equivalent to 2 large packages. We
// consider that the size of one large package is equivalent to the size of 4 small packages.
sig TruckStatus {
    drivenBy: Driver,
    content: set Package
} { maxPackPerTrack[content]}

pred maxPackPerTrack[p: set Package] {
    #p <= 2 or
    (#p < 8 and no pack:Package | pack.size = Large and p in pack) or
    (#p > 2 and #p = 5 and one pack:Package | pack.size = Large and pack in p)
}

sig Driver{}

sig WorkDay {
    whoDriveWhat: Driver -> Truck
} 

//Formalize the following constraint: a travel plan should never exceed the truck capacity
sig TravelPlan {
    thisDay: WorkDay,
    thisDayReq: some PickUpReq
}

fact noExceedCapacity {
    all t: TravelPlan | 
        maxPackPerTrack[t.thisDay.packagesToBeCollected]
}

sig Location{}

sig PickUpReq{
    origin: Location,
    packagesToBeCollected: Package  
}


// the driver have to drive different trucks on the same day
fact differentTruckPerDriverInADay {
    all day: WorkDay, t:Truck |
        #(day.whoDriveWhat.t) = 1 
}


pred show{
    #whoDriveWhat > 5 
}

run show for 5 but 6 int