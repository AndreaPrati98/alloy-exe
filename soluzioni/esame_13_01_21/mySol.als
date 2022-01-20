abstract sig Component {
    buff: set Event 
}
sig Topic{}

sig Event{
    topic: Topic
}

sig Publisher extends Component {
    topicsPublished: set Topic
} {#(buff) <= 10}

sig Subscriber extends Component{
    topicsSubscribed: set Topic
} {#(buff) <= 5 }

fact consistencyPub {
    all p:Publisher | 
        p.buff.topic in p.topicsPublished 
        // every topic in the published events are also 
        // in the publisher's topics published
        and
        //viceversa
        p.topicsPublished in p.buff.topic
}

fact consistencySub {
    all s:Subscriber | 
        s.buff.topic in s.topicsSubscribed
}

////////////////////////////////////////

assert cardinality {
    all p:Publisher, s:Subscriber |
        #(p.buff) <= 10 and #(s.buff) <= 5
}

check cardinality for 10

pred show{
    all s:Subscriber |
        #(s.buff) > 0 // at least one event in the buffer
}

run show for 5 but 1 Publisher, 6 int 