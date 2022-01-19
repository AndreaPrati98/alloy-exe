sig Network{
    uses: lone Network
}{ this not in uses}

sig  Node{
    belongsTo: one Network,
    isLinkedTo: some Node,
    isAttachedTo: lone Node
}{ this not in isAttachedTo and
   this not in isLinkedTo}

fact{
    no disj n1,n2:Node | 
        n2 in n1.isLinkedTo and
        n1.belongsTo != n2.belongsTo 
}

fact{
    all disj n1, n2:Node | 
    n2 in n1.isAttachedTo implies n1.belongsTo.uses = n2.belongsTo
}

fact {
    all node:Node | #(node.belongsTo.uses) = 1 implies 
        #(node.isAttachedTo) = 1
}

fact {
    no n:Network | #(belongsTo.n) = 0
}

pred show{}

// assert assert1{
    
// }

pred isReachable [n1: Node, n2:Node]{
    n2->n1 in ^isLinkedTo
}

pred isReachable_Prof [n1: Node, n2:Node]{
    n1 in n2.^isLinkedTo
}

assert corr{
    all disj n1,n2: Node |
    isReachable[n1,n2] <=> isReachable_Prof[n1,n2]
}
check corr

assert f1{
    all disj n1, n2:Node | n1 in n2.isLinkedTo implies 
    #(n1.belongsTo & n2.belongsTo) > 0
}

check f1 for 6

assert f2{
    all disj n1, n2:Node | n1 in n2.isAttachedTo implies #(n1.belongsTo & n2.belongsTo.uses) > 0
}
check f2 for 6


assert f3{
    all ntw: Network| some ntw2: Network | ntw2 in ntw.uses
    implies 
    all n:Node | n.belongsTo = ntw implies n.isAttachedTo != none
}

check f3 for 6

assert f4{
    all ntw: Network | some n:Node| n.belongsTo = ntw
}

check f4  for 6

run show 