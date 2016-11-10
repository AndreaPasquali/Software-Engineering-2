open util/boolean

sig Position {}

sig Car {
	idNumber: Int,
	batteryLevel: Int,
	position: one Position,
	available: Bool
}{
	idNumber>0
	0<=batteryLevel<=100
	all c1,c2: Car | (c1 != c2) => c1.idNumber != c2.idNumber //car's id numbers are unique
	all c1,c2: Car | (c1 != c2) => c1.position != c2.position //two cars cannot occupy the same position
}

sig RegistrationInfo {
	ssn: String,
	name: String,
	surname: String,
	phoneNumber: String,
	email: String,
	creditCardNumber: String,
	drivingLicenceNumber: String
}{
	all r1, r2: RegistrationInfo | (r1 != r2) => r1.ssn != r2.ssn) //a person cannot sign up twice
	all r1, r2: RegistrationInfo | (r1 != r2) => r1.phoneNumber != r2.phoneNumber) //two registrations cannot have the same phone number
	all r1, r2: RegistrationInfo | (r1 != r2) => r1.email != r2.email) //two registrations cannot have the same email
	all r1, r2: RegistrationInfo | (r1 != r2) => r1.drivingLicenceNumber != r2.drivingLicenceNumber) //two registration cannot have the same driving licence
	all r1, r2: RegistrationInfo | (r1 != r2) => r1.creditCardNumber != r2.creditCardNumber) //two registrations cannot havethe same credic card number
}

sig User {
	password: String,
	position: one Position,
	registrationInfo: RegistrationInfo
}{
	all u1, u2: User | (u1 != u2) => u1.registrationInfo != u2.registrationInfo) //two users cannot have the same registration info
}

sig Reservation {
	reservationTimer: Int, //expressed in seconds
	reservedCar: one Car,
	reservingUser: one User
}{
	0<=reservationTimer<=3600 //reservation timer of 1 hour
	reservationTimer>0 => reservedCar.available="false" //if a car is reserved, it is not available
}

sig SafeArea {
	positions: set Position,
	powerGridStations: set PowerGridStation 
}{
	all pgs : powerGridStations | pgs.position in positions //every power grid station position is contained in the set of positions of the safe area to which it belongs
}

sig PowerGridStation {
	position: one Positon,
	available: Bool
}{
	available="false" <=> one c: Car | c.position=position //a power grid station is unavailable when a car position matches its poisiton
}

sig Ride {
	car: one Car,
	reservation: one Reservation,
	duration: Int, //expressed in seconds
	passengers: Int,
	totalPrice: Int, //should be float
	terminated: Bool,
	endRidePosition: lone Position,
	moneySavingOptionActivated: Bool,
	moneySavingOptionInfo: lone MoneySavingOption,
	accidentReport: lone AccidentReport //after an accident report occours the ride ends
}{
	duration>0
	0>passengers>=5
	totalPrice>0
	(moneySavingOptionInfo=none) <=> moneySavingOptionActivated = "false" //money saving option info are present only if the opton has been activated
	terminated="false" => car.available="false" //the car is unavailable during the ride
	(endRidePosition != none) <=> terminated="true" //end ride position is saved only once the ride has been terminated
	(accidentReport = none && terminated="true") => (one sa: SafeArea | endRidePosition in sa.positions) //in order to terminate the ride the car must me parked in a safe area unless an accident occurs
	(accidentReport != none) => terminated="true" //the accident report implies the termination of the ride
	reservation.timer=0 //since the ride exists, the respective reservation is terminated
}

sig MoneySavingOption {
	startingPosition: Position,
	targetPosition: Position,
	selectedPowerGridStation: one PowerGridStation
}

sig AccidentReport {
	description: String
}

fact UsersCanJustRideOncePerTime {
	no r1,r2: Ride | r1.terminated="false" && r1.terminated="false" && r1.reservation.user=r2.reservation.user
}

fact PowerGridStationSelectedByMoneySavingOptionMustAlwaysBeAvailable{
	all r: Ride | (r.terminated="false" && moneySavingOptionActivated="true") => r.moneySavingOptionInfo.selectedPowerGridStation.available="true"
}
	
	
	
	
	
	
	
