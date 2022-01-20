abstract sig Table{
    tuples: set Tuple
}

sig PartTab extends Table{
    partitionedOn: some Node
} {#partitionedOn >= 2}

sig RepTab extends Table{
    replicatedOn: some Node
} 

sig Tuple{}

sig Node{
    repTuples: set Tuple,
    partTuple: disj set Tuple
}

////////////////////////////////////////////////

// the tuples of a RepTab are on all the nodes
fact replicatedOnAllNodes{
    all n: Node, t: RepTab |
        n in t.replicatedOn
}

// all the tuples on each node
// have to be present on a table.
// each tuple is contained in union of repTuples and partTuple
fact everyTupleInATab {
    all n:Node, t:Tuple| 
        t in (n.repTuples + n.partTuple) iff 
            (one tb:Table | t in tb.tuples)
}

// tutte le tuple su tutti i nodi, unite, saranno uguali a tutte le tuple 
fact noSpareTuples {
    all n: Node, t: Table |
        #(n.repTuples + n.partTuple) = #((n.repTuples + n.partTuple) & (t.tuples))
}

// all the tables in a RepTab has to be contained into all the nodes
// the table is replicated in
fact repTabConsistency {
    all t: RepTab, n: Node |
        t.replicatedOn = n implies 
            (t.tuples in n.repTuples)      
}

fact noDuplTuplesOnNodes {
    all disj n1,n2:Node |
        #(n1.tuples & n2.tuples) = 0
}