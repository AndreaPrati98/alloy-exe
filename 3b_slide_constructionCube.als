enum Size {Small, Medium, Large} 

sig Cube {
    size: Size,
    belongsTo: Tower,
    top: lone Cube 
} {top != this}

sig Tower {
    hasCubes: disj some Cube
}

// each cube belong to just one tower and that tower has 
// that cube 
fact oneCubeOneTower {
    all t: Tower | all c:Cube | 
        #(t.hasCubes & c) > 0 and
        #(c.belongsTo & t) > 0
} 

fact orderLargeMediumSmall{
    all c:Cube |
        c.size = Medium implies
            (c.top.size = Medium or 
            c.top.size = Small)
        else c.size = Small implies
            c.top.size = Small
            
}


pred show{}

run show