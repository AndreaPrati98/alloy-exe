sig Network {
    uses: lone Network
    /*
        un overlay usa una rete sotto, quindi questo parametro è 
        zero se la rete è underlay mentre è 1 se la rete è overlay
    */
} {this not in uses}

sig Node {
    belongsTo: Network,
    isLinkedTo: some Node,
    isAttachedTo: lone Node
} {this not in isAttachedTo and this not in isLinkedTo }

//Linked nodes have to be in the same network 
fact linkedNodesInTheSameNetwork {
    all disj n1, n2: Node | n1 in n2.isLinkedTo implies n1.belongsTo = n2.belongsTo
    /*
        (il prof lo scrive l'uguale in modo insiemistico facendo)
        #(n1.belongsTo & n2.belongsTo) > 0

        ovvero che l'intersezione non è vuota
    */
}

//A node belonging to a certain net can only be attached to nodes
// of the corresponding underlay net

// gli devo dire che, presi due nodi, il primo deve avere negli uses 
// la stessa net del nodo 2, per dire che sono della stessa net
fact isAttachedToInConnectedNetworks {
    all disj n1, n2: Node |
        n1 in n2.isAttachedTo implies
        #(n1.belongsTo & n2.belongsTo.uses) > 0
}

// if a net is an overlay one, then there should not be nodes in
// this net that are not attached to other nodes

// quindi tutti i nodi che sono in overlay avranno almeno un nodo attached
fact atLeastOneAttachedIfOverlayNet {
    all net : Network |
        #(net.uses) > 0 implies 
            all n:Node | n.belongsTo = net and #(n.isAttachedTo) > 0
}

// at least one node per each net
fact atLeastOneNodePerNet {
    all net:Network| some n:Node | n.belongsTo = net
    // all the nets, taken one or more nodes are equal to 
    // the net the nodes are in 
}

// Given a pair of nodes this pred is true if there exists a path
// from n2 to n1 alsi if through more nodes
pred isReachable[n1,n2:Node] {
    n1 in n2.^isLinkedTo
}

////////////////////////////////////////////////////////////////////////////////////

pred show{}

assert f3{
    all ntw: Network| some ntw2: Network | ntw2 in ntw.uses
    implies 
    all n:Node | n.belongsTo = ntw implies n.isAttachedTo != none
}



check f3 for 6

run show for 4 but 2 Network