open util/boolean

sig Char{}
sig Password{}
sig Email{}
sig DrivingLicence{}
sig CreditCard{}
sig PhoneNumber{}
sig Ssn{}

sig Position {}

abstract sig CarState {}
one sig Available, Unavailable, OutOfOrder extends CarState {}

sig Car {
	idNumber: Int,
	batteryLevel: Int,
	position: one Position,
	carState: CarState,
	inCharge: Bool
}{
	idNumber>0
	batteryLevel>=0
	batteryLevel<=100
}

fact CarIdNumbersAreUnique{
	all c1,c2: Car | (c1 != c2) => c1.idNumber != c2.idNumber
}

fact DifferentCarsCannotOccupySamePosition{
	all c1,c2: Car | (c1 != c2) => c1.position != c2.position
}

fact CarsInChargingOccupyOnePowerStation{
	all c: Car | c.inCharge.isTrue => (one ps: PowerStation | ps.position=c.position)
}

fact AvailableCarsMustBeInASafeArea{
	all c: Car | (one available: Available | available in c.carState) => (one sa: SafeArea | c.position in sa.positions)
}

sig RegistrationInfo {
	ssn: Ssn,
	name: seq Char,
	surname: seq Char,
	phoneNumber: PhoneNumber,
	email: Email,
	creditCardNumber: CreditCard,
	drivingLicenceNumber: DrivingLicence
}

fact PersonsCannotSignUpTwice{
	all r1, r2: RegistrationInfo | (r1 != r2) => (r1.ssn != r2.ssn)
}

fact SomeInfoCanBePartAtMostOfOneRegistation{
	all r1, r2: RegistrationInfo | (r1 != r2) => (r1.phoneNumber != r2.phoneNumber)
	all r1, r2: RegistrationInfo | (r1 != r2) => (r1.email != r2.email) 
	all r1, r2: RegistrationInfo | (r1 != r2) => (r1.drivingLicenceNumber != r2.drivingLicenceNumber)
	all r1, r2: RegistrationInfo | (r1 != r2) => (r1.creditCardNumber != r2.creditCardNumber)
}

sig User {
	password: seq Char,
	position: one Position,
	registrationInfo: one RegistrationInfo
}

fact DifferentUsersCannotHaveSameRegistrationInfo{
	all u1, u2: User | (u1 != u2) => (u1.registrationInfo != u2.registrationInfo)
}

sig Reservation {
	reservationTimer: Int, //expressed in seconds
	reservedCar: one Car,
	reservingUser: one User
}{
	reservationTimer>=0
	reservationTimer<=3600 //reservation timer of 1 hour
	reservationTimer>0 => (one unavailable: Unavailable | unavailable in reservedCar.carState) //if a car is reserved, it is not available
}

sig SafeArea {
	positions: set Position,
	powerGridStation: set PowerStation 
}{
	all ps: powerGridStation | ps.position in positions //every power station position is contained in the set of positions of the safe area to which it belongs
	#positions>=1
}

sig PowerStation {
	position: one Position,
	available: Bool
}{
	available.isFalse <=> (one c: Car | c.position=position) //a power grid station is unavailable when a car position matches its poisiton
}

fact DifferentPowerStationsHaveDifferentPositions {
	all ps1,ps2: PowerStation | ps1!=ps2 => ps1.position != ps2.position
}

sig Ride {
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
	passengers>0
	passengers<=5
	totalPrice>0
	(moneySavingOptionInfo=none) <=> moneySavingOptionActivated.isFalse //money saving option info are present only if the opton has been activated
	terminated.isFalse => (one unavailable: Unavailable | unavailable in reservation.reservedCar.carState) //the car is unavailable during the ride
	(endRidePosition != none) <=> terminated.isTrue //end ride position is saved only once the ride has been terminated
	(accidentReport = none && terminated.isTrue) => (one sa: SafeArea | endRidePosition in sa.positions) //in order to terminate the ride the car must me parked in a safe area unless an accident occurs
	(accidentReport != none) => terminated.isTrue //the accident report implies the termination of the ride
	reservation.reservationTimer=0 //since the ride exists, the respective reservation is terminated
}

sig MoneySavingOption {
	startingPosition: one Position,
	targetPosition: one Position,
	selectedPowerStation: one PowerStation
}

fact EveryMoneySavingOptionBelongsExactlyToOneRide{
	all mso: MoneySavingOption | one r: Ride | r.moneySavingOptionInfo=mso
}

sig AccidentReport {
	description: seq Char
}

fact UsersCanJustRideOncePerTime {
	no r1,r2: Ride | r1.terminated.isFalse && r2.terminated.isFalse && r1.reservation.reservingUser=r2.reservation.reservingUser
}

fact PowerStationSelectedByMoneySavingOptionMustAlwaysBeAvailable{
	all r: Ride | (r.terminated.isFalse && r.moneySavingOptionActivated.isTrue) => (r.moneySavingOptionInfo.selectedPowerStation.available.isTrue)
}

fact UnavailableCarsAreRunningOrReserved{
	all c: Car | (one unavailable: Unavailable | unavailable in c.carState) => ((one r: Ride | r.terminated.isFalse && r.reservation.reservedCar=c) || (one res: Reservation | res.reservationTimer>0 && res.reservedCar=c))
}

assert UsersHaveDifferentRegistrationInfo{
	no u1,u2: User | u1.registrationInfo=u2.registrationInfo
}

fact RunningsRidesAndReservationsCannotInvolveAvailableOrOutOfOrderCars{
	all c: Car | (one available: Available | available in c.carState) || (one outOfOrder: OutOfOrder | outOfOrder in c.carState)  => ((no r: Ride | r.reservation.reservedCar=c && r.terminated.isFalse) && (no res: Reservation | res.reservationTimer>0 && res.reservedCar=c))
}

pred show {
	#PowerStation=1
	#MoneySavingOption=1
}

run show
	
	
	
	
	
	
