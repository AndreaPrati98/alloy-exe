/*
Consider a transportation company that is organizing a package pick-up service.
The company has a certain number of trucks and drivers. All trucks have the same size. Each day, each
driver drives a single truck (the same driver can drive different trucks in different days).
A pick-up request is specified by the origin and the size of the package (for simplicity, assume there are
only two sizes, small and large).
A travel plan is associated with a driver and a truck in a certain day and is defined in terms of the packages
that must be collected by that driver during the day, using the specified truck.
*/

// Quest A
//Define suitable Alloy signatures – and any related constraints – to describe the problem above

// Quest B
// Define a signature TruckStatus that represents the snapshot of a truck, that is, the truck with its current
// content and current driver. Ensure that the following constraint holds: a truck never exceeds its maximum
// capacity, which corresponds to an amount of packages whose size is equivalent to 2 large packages. We
// consider that the size of one large package is equivalent to the size of 4 small packages.

// Quest C
// Formalize the following constraint: a travel plan should never exceed the truck capacity.

// Quest D
// Formalize the following constraint: drivers and trucks cannot be assigned to multiple travel plans in the
// same day

sig TruckSize{}
sig Truck{
    size: TruckSize
}

sig Day{}
sig Driver{}

sig TravelPlan {
    day: Day,
    driver: Driver,
    usedTruck: Truck,
    packToBeCarried: set PickUpReq 
}

abstract sig PackSize{}
one sig Small, Large extends PackSize{}
sig Location{}
sig PickUpReq{
    origin: Location,
    packSize: PackSize
}

sig TruckStatus {
    t: Truck,
    currentDriver: Driver,
    content: set PickUpReq
} {trackCapacity[content]}

fact respectTruckCapacity {
    all t:TravelPlan | 
        trackCapacity[t.packToBeCarried]
}

fact noTruckSameDay {
    no disj t1, t2: TravelPlan | 
        (t1.usedTruck = t2.usedTruck and t1.day = t2.day) or
        (t1.driver = t2.driver and t1.day = t2.day)

}

pred trackCapacity[packs: set PickUpReq] {
    #packs <= 2 or
    ((#packs > 6 and #packs <= 8) and no p: PickUpReq | p in packs and p.packSize = Large) or
    ((#packs > 2 and #packs > 5) and one p:PickUpReq | p in packs and p.packSize = Large)        
}

pred show{
    #(TravelPlan.driver) > 2 
}

run show for 6 int