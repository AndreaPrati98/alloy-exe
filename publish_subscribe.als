abstract sig Component{}

sig Publisher extends Component{
    publishEventOf: some Topic,
    eventsToBeSent: set Event
}

sig Subscriber extends Component{
    subscribedTo: some Topic,
    incomingEvents: set Event
}

sig Configuration{
    publishers: some Publisher,
    subscribers: some Subscriber
}

sig Topic{}
sig Event{
    topic: Topic
}

fact buffer_publisher{
    all p:Publisher | #(p.eventsToBeSent) <= 10
}


fact buffer_subscriber{
    all s:Subscriber | #(s.incomingEvents) <= 5
}

fact consistency_subscriber{
    all s:Subscriber, e:Event |
    e in s.incomingEvents => e.topic in s.subscribedTo
}


fact consistency_publisher{
    all p:Publisher, e:Event |
    e in p.eventsToBeSent => e.topic in p.publishEventOf
}

pred SubscribeToTopic[c,c_up:Configuration, s,s_up:Subscriber, t:Topic]{
    //Precondition
    s in c.subscribers
    not (t in s.subscribedTo)
    //Postcondition
    s_up.incomingEvents = s.incomingEvents
    s_up.subscribedTo = s.subscribedTo + t
    
    c_up.publishers = c.publishers
    c_up.subscribers = c.subscribers - s + s_up 
}

pred show{
    #Publisher > 1
    
}


pred eventDispatched[c,c_up:Configuration,e:Event,s,s_up:Subscriber]{
    //Precondition

    s in c.subscribers
    
    e in c.publishers.eventsToBeSent    // Qualuno lo deve avere in coda per inviarlo
    not ( e in s.incomingEvents)        // L'evento non è ancora stato ricevuto
    #(s.incomingEvents) <=4             // Deve esserci spazio in buffer
    e.topic in s.subscribedTo           // Il topic è nella lista a cui sono iscritto

    //Postcondition

    // Il nuovo subscriber dopo il dispatch è iscritto agli stessi topic,
    // ma nel buffer ha in coda il nuovo evento
    s_up.incomingEvents = s.incomingEvents + e
    s_up.subscribedTo = s.subscribedTo

    // La nuova configurazione ha gli stessi publishers ma 
    // I subscribers sono diversi
    c_up.publishers = c.publishers
    c_up.subscribers = c.subscribers - s + s_up 
}

run show for 2 but 6 int

run SubscribeToTopic for 6 int