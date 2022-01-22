abstract sig Bool{}
one sig True extends Bool {}
one sig False extends Bool {}


sig Tuple{}

sig Table{
    tuple: set Tuple,
    isPartitioned: Bool,
    isReplicated: Bool
}{
    isPartitioned = True implies isReplicated = False
    isReplicated = True implies isPartitioned = False
}

sig Node{
    contains: set Tuple
}
one sig Database {
    tables: some Table,
    nodes: some Node
}
fact{
    //Se ho una tabella nel db tutte le sue tuple devono essere nei nodi
    all t:Table, d:Database | 
    t in d.tables implies t.tuple in d.nodes.contains
}

fact p1{
    //Partitioned = nessun nodo le contiene tutte
    all t:Table | t.isPartitioned = True implies (no n:Node | (n.contains & t.tuple) = t.tuple)
}

fact partitioned{
    all t:Table,n:Node, d:Database |
    t.isPartitioned = True implies 
        (no disj n1,n2:Node |
            #(n1.contains & t.tuple) > 0 and
            #(n2.contains & t.tuple) > 0 and
            (n1.contains & n2.contains) in t.tuple
        )

}

fact f1{
    all t:Table | 
    t.isReplicated = True implies #(contains.(t.tuple)) >=2 
}

