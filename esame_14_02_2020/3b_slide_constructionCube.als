/*
	Actual circulating trains, where each train belongs to a line and has an actual crowdedness level
	and a detected crowdedness level (where the crowdedness level, actual or detected, can be
	“sparse”, “normal”, “crowded”, “overflowing”).
	
	Travelers, who take trains. Users of TSPmonitor, who have a list of preferred train lines, 
	which they regularly take Users create reports on the crowdedness level of trains. 
	For simplicity, we consider that each user produces at most one report per train.
	Users receive notifications from the system, where each notification concerns only trains of their
	preferred lines, and it contains the detected crowdedness level of the train. For simplicity, we
	consider that each user receives only one notification per train.
*/

sig Train{
	belongTo: Line,
	crowdenessLv: CrowdStatus
}

abstract sig Person{}

sig Traveler extends Person {
	trainTaken: Train
}

sig TSPuser extends Person {
	reportCreated: lone Report,
	preferredLine: set Line,
	actuallyOnTrain: Train,
	notificationRecieved: set Notification
}

sig Report{
	trainReported: Train,
	reportCrowdState: CrowdStatus
}

sig Notification {
	lineNotified: Line
}

abstract sig CrowdStatus{}
one sig sparse, normal, crowded, overflowing extends CrowdStatus{}

sig Line{
	trainsOfTheLine: set Train
}

fact notifyPreferredLine {
	all u: TSPuser, n:Notification | n in u.notificationRecieved iff n.lineNotified in u.preferredLine
}

fact mutualLineTrain{
	all t:Train, l:Line | (t in l.trainsOfTheLine) iff (l in t.belongTo)
}

// it s possible to report only if you are actually on that train
fact reportOnlyIfYouInTheTrain {
	all r: Report, u: TSPuser | ((r & u.reportCreated) > 0) implies (r.trainReported = u.actuallyOnTrain)
}

/*
Formalize through a predicate the following goal: users are informed about the actual crowdedness
level of the trains of their preferred lines.
*/
pred usersInformedAboutPrefLines{
	all u: TSPuser | u.notificationReceived.lineNotified in 
	
}
