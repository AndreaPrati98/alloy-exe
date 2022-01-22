// Model cubes and cube piles

abstract sig Size{}
one sig Small, Medium, Large extends Size {}

sig Cube {
    size: Size,
    belongsTo: lone Tower,
    top: lone Cube 
} {top != this}

sig Tower {
    hasCubes: some Cube
}

// A Lagrge cube can have at its top another cube of whatever size, while a
// Medium cube can carry another Medium or a Small and, at the end, 
// a Small cube can carry just a Small cube
fact pilingOrder{
	all c: Cube | 
		(c.top.size = Large implies c.size = Large) and
		(c.top.size = Medium implies (c.size != Small))		
}

assert respectedPilingOrder {
	no c: Cube | c.size = Small and (c.top.size = Medium  or c.top.size = Large)
}

//check respectedPilingOrder for 10 but 6 int

pred show{}

run show for 10 but 2 Tower, 6 int
