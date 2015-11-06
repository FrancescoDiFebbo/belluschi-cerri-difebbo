// ALLOY CODE FOR MYTAXSERVICE

// This util defines True or False boolean
open util/boolean

// Dates are expressed as the number of seconds from 1970-01-01 

//SIGNATURES

sig Strings{}

abstract sig User {
	email : one Strings,
	emailConfirmed: one Bool,
	username: one Strings,
	password: one Strings,
	name: one Strings,
	surname: one Strings,
	address: lone Strings,
	telephoneNumber: lone Strings
}

sig Passenger extends User{

}

sig TaxiDriver extends User{
	licenseID: one Int, 
	taxiPlateNumber: one Strings,
	taxiCode: one Int,
	numberOfSeats: one Int,
	status: one TaxiDriverStatus
}
{
	taxiCode > 0
	licenseID > 0
	numberOfSeats > 0
}

abstract sig TaxiDriverStatus {}
sig READY extends TaxiDriverStatus {}
sig BUSY extends TaxiDriverStatus {}
sig OFFLINE extends TaxiDriverStatus {}

sig Float{
}

sig Position {
	latitude: one Float,
	longitude: one Float,
	zone: one TaxiZone,
}

abstract sig RideStatus{}
sig ONGOING extends RideStatus {}
sig COMPLETED extends RideStatus {}

sig Ride {
	startPosition:one Position,
	endPosition:one Position,
	startDate:one Int,
	endDate:lone Int,
	status: one RideStatus,
	taxiDriver: one TaxiDriver,
	passengers: some Passenger,
	numOfPassengers: one Int,
    requests: some RideRequest
}
{
	#requests > 0
	startDate > 0
	startDate < endDate
	startPosition!=endPosition
	numOfPassengers <= taxiDriver.numberOfSeats
	#passengers <= numOfPassengers
	#endDate=0 iff status= ONGOING
	#endDate=1 iff status= COMPLETED
}

abstract sig RideRequestStatus{}
sig PENDING extends RideRequestStatus {}
sig ACCEPTED extends RideRequestStatus {}

sig RideRequest{
	startPosition: one Position,
	endPosition: lone Position,
	requestDate: Int,
	ride: lone Ride,
	//passenger that requests the ride
	passenger: one Passenger,
	//additional passengers specified in the request
	numberOfPassengers: one Int,
	taxiDriver: lone TaxiDriver,
	status: one RideRequestStatus,
	isShared: one Bool
}
{
	endPosition != startPosition
    isShared = False implies #endPosition= 0
	(#ride=0 or #taxiDriver=0) iff status = PENDING
	(#ride=1 and #taxiDriver=1) iff status = ACCEPTED
	requestDate>0
	numberOfPassengers > 0
}

sig ReserveRideRequest extends RideRequest{
	startDate: one Int
}
{
	#endPosition=1
}
	
sig TaxiZone{
	zoneId: Int,
	queue: one Queue,
	positions: set Position
}

sig Queue {
	zone: one TaxiZone,
	taxiDrivers: set TaxiDriver
}

// FACTS

// users must not have same username or same e-mail
fact UniqueUser{
	no u1, u2: User | (u1 != u2 and (u1.username = u2.username or u1.email = u2.email))
}

// taxi drivers must not have same licenseID or same taxiCode
fact UniqueTaxiDriver{
	no t1, t2: TaxiDriver | (t1 != t2 and (t1.licenseID = t2.licenseID or t1.taxiCode=t2.taxiCode))
}

//if a taxi driver has the status READY, he/she has to put into some queues
fact QueuesForReadyTaxiDriver{
	all t: TaxiDriver | ((t.status = READY)  iff (some q: Queue | t in q.taxiDrivers))
}

//if a taxi is in a queue must be only in one of them
fact TaxiDriverInOnlyOneQueue {
	all t: TaxiDriver | (lone q: Queue | t in q.taxiDrivers)
}
//a taxi must be BUSY during the time of the ride
fact BusyDuringRide {
	all t: TaxiDriver, r: Ride| (r.taxiDriver = t and #endDate=0)
		implies (t.status= BUSY)
}

//zones must not have same zoneId
fact UniqueTaxiZone {
	no z1, z2: TaxiZone |( z1 != z2 and z1.zoneId = z2.zoneId)
	queue = ~zone
}

//a passenger cannot take two ride at the same time
fact noPassengerOverlapRide {
	all p: Passenger, r1, r2: Ride | (p in r1.passengers and p in r2.passengers and r1 != r2)
		implies (r1.endDate < r2.startDate or r2.endDate < r1.startDate)
}

//a taxi driver cannot take two ride at the same time
fact noTaxiDriverOverlapRide {
	all t: TaxiDriver, r1, r2: Ride | (t in r1.taxiDriver and t in r2.taxiDriver and r1 != r2)
		implies (r1.endDate < r2.startDate or r2.endDate < r1.startDate)
}

// only ACCEPTED Ride Request can have a Ride
fact RideWithOnlyAcceptedRideRequest{
	all r: Ride, rr: r.requests| rr.ride = r and rr.status = ACCEPTED  
}

//a Ride Request cannot be in two different Ride 
fact RideWithOnlyAcceptedRideRequest{
	 no  r1,r2 :Ride | r1!=r2 and (r1.requests=r2.requests)
}

//A ride that has more than one RideRequest must have all RideRequest shared
fact RideWithRequestsSharing {
	all r: Ride| (#r.requests>1)
		iff (all rr:r.requests|(rr.isShared = True ))
}

//if a ride refers to a ride request the taxi driver must be the same
fact taxiDriverUniqueRideRefersRideRequest {
	all rr: RideRequest | rr.ride.taxiDriver = rr.taxiDriver 
}

//if a ride refers to a ride request the passenger of the Ride Request must be in the passenger of the Ride
fact passengersUniqueRideRefersRideRequest {
	all rr: RideRequest , r:Ride|  rr.ride = r implies rr.passenger in r.passengers
}

//if a ride refers to a ride request the start destination must be the same
fact destinationUniqueRideRefersRideRequest {
	all rr: RideRequest , r:Ride|  rr.ride = r implies rr.startPosition = r.startPosition
}

//the number of passengers in the request refers to the corrispondent ride must be the same
fact correspondentNumberOfPassengers {
	all rr: RideRequest , r:Ride|  rr.ride = r implies rr.ride.numOfPassengers = sum ( r.requests.numberOfPassengers)
}

//a passenger cannot take another request when is in a ongoing ride
fact noPassengerOverlapRideRequest {
	all p: Passenger, r1, r2: RideRequest | (p = r1.passenger and p = r2.passenger and r1 != r2)
		implies (r1.ride.endDate < r2.ride.startDate or r2.ride.endDate < r1.ride.startDate)
}

//the request date of a request ride must be before the start date of a ride 
fact requestDateBeforeRide{
	all r: RideRequest | r.requestDate<r.ride.startDate
}


//the reserve date of a reserve ride must be before the start date of a ride and after the request date
fact reserveDateBeforeRide{
	all r: ReserveRideRequest | r.startDate<r.ride.startDate and r.startDate>r.requestDate
}


// ASSERTION 

//all taxi in at maximum one queue
assert TaxiDriverInOneQueue {
	all t: TaxiDriver | (lone q: Queue | t in q.taxiDrivers)
}

//check TaxiDriverInOneQueue 
//No counterexample found. Assertion may be valid

//No another ride if the taxi driver is busy
assert noAnotherRideIfTaxiDriverBusy {
	all  r1, r2: Ride | (r1.taxiDriver=r2.taxiDriver and r1 != r2)
		implies (r1.endDate < r2.startDate or r2.endDate < r1.startDate)
}

//check noAnotherRideIfTaxiDriverBusy
//No counterexample found. Assertion may be valid

//No another ride if the passenger is going in another ride
assert noAnotherRideIfPassengerIsGoingInAnotherRide {
	all  r1, r2: Ride | (r1.passengers=r2.passengers and r1 != r2)
			implies (r1.endDate < r2.startDate or r2.endDate < r1.startDate)
}
//check noAnotherRideIfPassengerIsGoingInAnotherRide
//No counterexample found. Assertion may be valid


// PREDICATES


pred showNormalRequest(){
	#Passenger =1
	#Ride = 1
	#TaxiDriver = 1
}

run showNormalRequest for 3

pred show(){
	#Passenger >= 2
	#Ride >= 2
	#TaxiDriver >= 2
    #{x: Ride| #x.requests>1} >=1
	#{x: RideRequest | x.isShared = True} > 1
}

run show for 4

