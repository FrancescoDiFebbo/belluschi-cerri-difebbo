// ALLOY CODE FOR MYTAXSERVICE


//SIGNATURES
sig Strings{}

abstract sig User {
email : one Strings,
username: one Strings,
password: one Strings,
name: one Strings,
surname: one Strings,
address: one Strings,
telephoneNumber: one Strings
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
}

abstract sig RideStatus{}
sig ONGOING extends RideStatus {}
sig COMPLETED extends RideStatus {}

sig Ride {
	startPosition: Position,
	endPosition: Position,
	//Much easier if with put Int instead of Date
	startDate: Int,
	endDate: Int,
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
	numOfPassengers <= taxiDriver.numberOfSeats
	#passengers <= numOfPassengers
}

abstract sig RideRequestStatus{}
sig SEARCHING extends RideRequestStatus {}
sig ACCEPTED extends RideRequestStatus {}

sig RideRequest{
	startPosition: one Position,
	requestDate: Int,
	passenger: one Passenger,
	numberOfPassengers: one Int,
	taxiDriver: one TaxiDriver,
	status: one RideRequestStatus
}
{
	requestDate>0
	numberOfPassengers > 0
}

//TODO overlap extends
sig ReserveRideRequest extends RideRequest{
	startDate: one Int,
	endPosition: one Position
}
{
	startDate >0
}

sig ShareRideRequest extends RideRequest{
	endPosition: one Int
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

//zones must not have same zoneId
fact UniqueTaxiZone {
	no z1, z2: TaxiZone |( z1 != z2 and z1.zoneId = z2.zoneId)
	queue = ~zone
}

//if a taxi driver has the status READY, he/she has to put into a queue (only one)

//a taxi must be busy during the time of the ride

//a passenger cannot take two ride at the same time
fact noPassengerOverlapRide {
	all p: Passenger, r1, r2: Ride | (p in r1.passengers
		and p in r2.passengers and r1 != r2)
		implies
		(r1.endDate < r2.startDate or r2.endDate < r1.startDate)
}

//a taxi driver cannot take two ride at the same time
fact noTaxiDriverOverlapRide {
	all t: TaxiDriver, r1, r2: Ride | (t in r1.taxiDriver
		and t in r2.taxiDriver and r1 != r2)
		implies
		(r1.endDate < r2.startDate or r2.endDate < r1.startDate)
}


//a position in a zone must not be position in any other zone 

//if the status of a ride request is SEARCHING the value of the Taxi Driver must be null

//if the status of a ride request is ACCEPTED there must be a RideRequest in Request

// PREDICATES

pred show(){
	#Passenger > 1
	#Ride > 1
	#TaxiDriver > 1
}

run show for 4
