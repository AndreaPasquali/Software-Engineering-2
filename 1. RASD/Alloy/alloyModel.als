open util/boolean

sig Char{}
sig Name{}
sig Surname{}
sig Password{}
sig Email{}
sig DrivingLicence{}
sig CreditCard{}
sig PhoneNumber{}
sig Ssn{}

abstract sig Position {} 

abstract sig CarState {}
one sig Available, Unavailable, OutOfOrder extends CarState {}

abstract sig BatteryLevel {}
one sig Zero,Low, Medium, High extends BatteryLevel{}

sig Car {
	idNumber: Int,
	batteryLevel: BatteryLevel,
	position: one Position,
	carState: CarState,
	inCharge: Bool
}{
	idNumber>0
	(one unavailable: Unavailable | unavailable in carState) => ( ((one res: Reservation | res.expired.isFalse && res.reservedCar=this) && (no ride: Ride | ride.terminated.isFalse && ride.reservation.reservedCar=this)) ||
																										((one ride: Ride | ride.terminated.isFalse && ride.reservation.reservedCar=this) && (no res: Reservation | res.expired.isFalse && res.reservedCar=this)) ) //unavailable means that the car has been reserved or is riding
	(one outOfOrder: OutOfOrder | outOfOrder in carState) => ((no ride: Ride | ride.terminated.isFalse && ride.reservation.reservedCar=this) && (no res: Reservation | res.expired.isFalse && res.reservedCar=this)) //outOforder means that the car cannot be reserved
}

fact UsersCannotReserveOutOfBatteriesCars{
	no res: Reservation | res.expired.isFalse && (one zero: Zero | zero in res.reservedCar.batteryLevel)
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
	ssn: one Ssn,
	name: one Name,
	surname: one Surname,
	phoneNumber: one PhoneNumber,
	email: one Email,
	creditCardNumber: one CreditCard,
	drivingLicenceNumber: one DrivingLicence
}

fact AllRegistrationInfoAreRelatedToOneUser{
	all ri: RegistrationInfo | (one u: User | u.registrationInfo=ri)
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
	password: one Password,
	position: one Position,
	registrationInfo: one RegistrationInfo
}

fact DifferentUsersCannotHaveSameRegistrationInfo{
	all u1, u2: User | (u1 != u2) => (u1.registrationInfo != u2.registrationInfo)
}

sig Reservation {
	expired: Bool,
	reservedCar: one Car,
	reservingUser: one User
}{
	expired.isFalse=> (one unavailable: Unavailable | unavailable in reservedCar.carState) //if a car is reserved, it is not available
}

sig SafeArea {
	positions: disj set Position,
	powerGridStation: set PowerStation 
}{
	all ps: powerGridStation | ps.position in positions //every power station position is contained in the set of positions of the safe area to which it belongs
	#positions>=1
}

//the set of positions in the range of 3 km from a power station
sig NonFineArea{
	positions: set Position
}{
	some pos: positions | (one ps: PowerStation | ps.position=pos)
	all pos: positions | (one sa: SafeArea | pos in sa.positions)
}

fact AllPowerStationsAreInANonFineArea{
	all ps: PowerStation | some nfa: NonFineArea | ps.position in nfa.positions
}

sig PowerStation {
	position: one Position,
	available: Bool
}{
	available.isFalse <=> (one c: Car | c.position=position && c.inCharge.isTrue) //a power grid station is unavailable when a car position matches its poisiton and tha car is in charge
}


fact PowerStationsMustBeInASafeArea{
	all ps: PowerStation | (one sa: SafeArea | ps.position in sa.positions)
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
	endRideBatteryLevel: lone BatteryLevel,
	endRideIsInCharge: one Bool,
	moneySavingOptionActivated: Bool,
	moneySavingOptionInfo: lone MoneySavingOption,
	accidentReport: lone AccidentReport //after an accident report occours the ride ends
}{
	duration>0
	passengers>0
	passengers<=5
	totalPrice>0
	(moneySavingOptionInfo=none) <=> moneySavingOptionActivated.isFalse //money saving option info are present only if the opton has been activated
	terminated.isFalse => (one unavailable: Unavailable | unavailable in reservation.reservedCar.carState) && (reservation.reservedCar.inCharge.isFalse) //the car is unavailable during the ride and cannot be in charge
	(endRidePosition != none) <=> terminated.isTrue //end ride position is saved only once the ride has been terminated
	(accidentReport = none && terminated.isTrue) => (one sa: SafeArea | endRidePosition in sa.positions) //in order to terminate the ride the car must me parked in a safe area unless an accident occurs
	(accidentReport != none) => terminated.isTrue //the accident report implies the termination of the ride
	reservation.expired.isTrue //since the ride exists, the respective reservation is terminated
	terminated.isTrue => (endRidePosition!=none && endRideBatteryLevel!=none && endRideIsInCharge!=none) //whenever a ride is terminated all the field releted to the end of the ride are not empty
	endRideIsInCharge.isTrue => (one ps:PowerStation | endRidePosition=ps.position)
}

fact OneReservationIsRelatedAtMostToOneRide{
	all res: Reservation | lone ride: Ride | ride.reservation=res
}

sig MoneySavingOption {
	startingPosition: one Position,
	targetPosition: one Position,
	selectedPowerStation: one PowerStation
}{
	startingPosition != targetPosition
}

fact EveryMoneySavingOptionBelongsExactlyToOneRide{
	all mso: MoneySavingOption | one r: Ride | r.moneySavingOptionInfo=mso
}

sig AccidentReport {
	description: seq Char
}

fact AccidentReportMustBeRelatedToAnAccident {
	all ar: AccidentReport | one ride:Ride | ride.accidentReport=ar
}

fact UsersCanJustRideOncePerTime {
	no disj r1,r2: Ride | r1.terminated.isFalse && r2.terminated.isFalse && r1.reservation.reservingUser=r2.reservation.reservingUser
}

fact PowerStationSelectedByMoneySavingOptionMustAlwaysBeAvailable{
	all r: Ride | (r.terminated.isFalse && r.moneySavingOptionActivated.isTrue) => ((r.moneySavingOptionInfo.selectedPowerStation.available.isTrue)&&(no car:Car | r.moneySavingOptionInfo.selectedPowerStation.position!=car.position))
}

assert RunningsRidesAndReservationsCannotInvolveAvailableOrOutOfOrderCars{
	all c: Car | (one available: Available | available in c.carState) || (one outOfOrder: OutOfOrder | outOfOrder in c.carState)  => ((no r: Ride | r.reservation.reservedCar=c && r.terminated.isFalse) && (no res: Reservation | res.expired.isFalse && res.reservedCar=c))
}

assert UnavailableCarsAreRunningOrReserved{
	all c: Car | (one unavailable: Unavailable | unavailable in c.carState) => ((one r: Ride | r.terminated.isFalse && r.reservation.reservedCar=c) || (one res: Reservation | res.expired.isFalse && res.reservedCar=c))
}

assert PowerStationsBelongToOneSafeAre{
	no disj sa1,sa2: SafeArea | some ps: PowerStation | ps in sa1.powerGridStation && ps in sa2.powerGridStation
}

assert NumberOfReservationsGreaterOrEqualThenNumberOfRides{
	#Reservation>=#Ride
}

assert ACarCannotBeInvolvedInTwoNonTerminatedRides{
	no disj r1,r2: Ride | r1.terminated.isFalse && r2.terminated.isFalse && r1.reservation.reservedCar=r2.reservation.reservedCar
}

assert ReservedCarsCannotBeInvolvedInANonTerminatedRide{
	no car: Car | (one res: Reservation | res.expired.isFalse && res.reservedCar=car) && (some ride: Ride | ride.terminated.isFalse && ride.reservation.reservedCar=car)
}

assert RunningCarsCannotBeInCharge{
	no car: Car | car.inCharge.isTrue && (one ride: Ride | ride.terminated.isFalse && ride.reservation.reservedCar=car)
}

assert CarsInChargingAreInANonFineArea{
	all car:Car | car.inCharge.isTrue => (some nfa: NonFineArea | car.position in nfa.positions)
}

pred MoneySavingOptionBonusAchieved(r: Ride){
	r.terminated.isTrue &&
	r.moneySavingOptionActivated.isTrue &&
	r.moneySavingOptionInfo.selectedPowerStation.position=r.endRidePosition &&
	r.endRideIsInCharge.isTrue &&
	r.accidentReport=none
}

pred ChargingBonusAchieved(r:Ride){
	r.terminated.isTrue &&
	r.endRideIsInCharge.isTrue &&
	r.accidentReport=none
}

pred FineForParkingInAFineArea(r: Ride){
	r.terminated.isTrue &&
	r.accidentReport=none &&
	no nfa: NonFineArea | r.endRidePosition in nfa.positions
}

pred PassengersBonusAchieved(r: Ride){
	r.terminated.isTrue &&
	r.passengers>=2 &&
	r.accidentReport=none &&
	one nfa: NonFineArea | r.endRidePosition in nfa.positions &&
	(one medium: Medium | medium in r.endRideBatteryLevel)
}

pred HighBatteryBonusAchieved(r: Ride){
	r.terminated.isTrue &&
	r.endRideIsInCharge.isFalse &&
	one nfa: NonFineArea | r.endRidePosition in nfa.positions &&
	one high: High| high in r.endRideBatteryLevel &&
	r.accidentReport=none
}

pred FineForLowBattery(r:Ride){
	r.terminated.isTrue &&
	r.endRideIsInCharge.isFalse &&
	one low:Low | low in r.endRideBatteryLevel &&
	r.accidentReport=none
}

pred showPred1{
	one ride: Ride | MoneySavingOptionBonusAchieved[ride] &&
	one ride: Ride | ChargingBonusAchieved[ride]
}

pred showPred2{
	one ride: Ride | FineForParkingInAFineArea[ride] &&
	one ride: Ride | PassengersBonusAchieved[ride]
}

pred showPred3{
	one ride: Ride | HighBatteryBonusAchieved[ride] &&
	one ride: Ride | FineForLowBattery[ride]
}
 
run showPred1
run showPred2
run showPred3
check RunningsRidesAndReservationsCannotInvolveAvailableOrOutOfOrderCars
check UnavailableCarsAreRunningOrReserved
check PowerStationsBelongToOneSafeAre
check NumberOfReservationsGreaterOrEqualThenNumberOfRides
check ACarCannotBeInvolvedInTwoNonTerminatedRides
check ReservedCarsCannotBeInvolvedInANonTerminatedRide
check RunningCarsCannotBeInCharge
	
	
	
	
	
