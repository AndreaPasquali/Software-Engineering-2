/*return the best power station where to plug in the car,
according to the distribution of the cars and the final destination.
Throws an exception if no suitable power station is found.*/
PowerStation moneySavingOption(Positon finalDestination, int r, SafeArea[] safeAreas){
    SafeArea[] validSafeAreas;
    foreach(SafeArea safeArea in safeAreas)
        if(!safeArea.getAvailablePowerStations().isEmpty())
            validSafeAreas.add(safeArea);
    sortByParkedCars(validSafeAreas);
    foreach(SafeArea safeArea in validSafeArea)
        if(distance(safeArea, finalDestination) < r)
            return safeArea.getAvailablePowerStations.get(0);
    throw new Exception("no power station found");
}

void sortByParkedCars(SafeArea[] s){
    //uses quickSort in order to sort the safe areas in O(NlogN)
}

int distance(SafeArea s, Position p){
    //return the minimum distance in meters between a given position and a given safe area
}