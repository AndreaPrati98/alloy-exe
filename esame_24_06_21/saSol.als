enum sizePackage { small, large}

one sig TruckSize{}

sig Driver{}

sig Truck{
    size: TruckSize,
    content: set Package
}

sig TruckStatus{
    truck: Truck,
    content: set Package,
    driver: Driver
}

sig Package{
    packSize: sizePackage
}

sig Day{}

sig TravelPlan{
    driver: Driver,
    truck: Truck,
    currentDay: Day,
    packagesToPick: some Package
}

fact f1 {
    no disj tp1,tp2: TravelPlan | 
    tp1.currentDay = tp2.currentDay and
        (tp1.driver = tp2.driver or 
         tp1.truck = tp2.truck )
}

fact truck{
    no t:Truck |
    #(t.content) > 2 and
    #(t.content.packSize & large) > 2
}

fact{
    all t:Truck |
    #(t.content) <= 4
    and
    #(t.content.packSize & large) <= 2 and
    #(t.content.packSize & small) <= 4 and
    #(t.content) = 3 implies ( #(t.content.packSize & large) <= 1 ) and
    #(t.content) = 4 implies ( #(t.content.packSize & large) <= 2 ) 
}

fact{
    all ts:TruckStatus | 
    #(ts.content) <= 4
    and
    #(ts.content.packSize & large) <= 2 and
    #(ts.content.packSize & small) <= 4 and
    #(ts.content) = 3 implies ( #(ts.content.packSize & large) <= 1 ) and
    #(ts.content) = 4 implies ( #(ts.content.packSize & large) <= 2 )
}

fact f3{
    all tp: TravelPlan| 
    #(tp.packagesToPick) <= 4
    and
    #(tp.packagesToPick.packSize & large) <= 2 and
    #(tp.packagesToPick.packSize & small) <= 4 and
    #(tp.packagesToPick) = 3 implies ( #(tp.packagesToPick.packSize & large) <= 1 ) and
    #(tp.packagesToPick) = 4 implies ( #(tp.packagesToPick.packSize & large) <= 2 )
}




