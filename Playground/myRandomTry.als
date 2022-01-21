abstract sig Person{

} 

sig Man extends Person {
    hasWife: Woman
}
sig Woman extends Person{
    hasHusband: Man
}

fact atLeastOneManAndOneWoman {
    #Man >= 1 and #Woman >= 1
}

pred show{}

run show for 6 int