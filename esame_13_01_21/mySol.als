abstract sig Component {
    buff: set Event 
}
sig Topic{}

sig Event{
    topic: Topic
}

sig Configuration {
    publishers: set Publisher,
    subscribers: set Subscriber
}

sig Publisher extends Component {
    topicsPublished: set Topic
} {#(buff) <= 10}

sig Subscriber extends Component{
    topicsSubscribed: set Topic
} {#(buff) <= 5 }

//////////////////////////////////////////

fact consistencyConfig {
    all c: Configuration |
        c.subscribers.buff in c.publishers.buff
}

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
    all c:Configuration |
        #(c.subscribers.buff) > 0
}

run show for 5 but 1 Configuration, 6 int 