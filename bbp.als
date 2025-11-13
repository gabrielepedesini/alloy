// ===========================================
// SIGNATURES
// ===========================================

abstract sig User {}

sig NonRegisteredUser extends User {}

sig RegisteredUser extends User {
    email: one String,
    paths: set Path,
    trips: set Trip,
    favoritePaths: set Path
}

sig Path {
    owner: one RegisteredUser,
    visibility: one Visibility
}

sig Trip {
    owner: one RegisteredUser
}

abstract sig Visibility {} 

sig Private, Public extends Visibility {}


// ===========================================
// FACTS
// ===========================================

// Ensure unique emails for RegisteredUsers
fact UniqueEmails {
    all ru1, ru2: RegisteredUser | 
        ru1 != ru2 implies ru1.email != ru2.email
}

// Ensure that RegisteredUsers and NonRegisteredUsers are disjoint sets
fact DisjointUsers {
    no RegisteredUser & NonRegisteredUser
}

// Ensure that NonRegisteredUsers do not have paths, trips, or favorite paths
fact NonRegisteredUsersHaveNothingAssociated {
    all nru: NonRegisteredUser |
        no { p: Path | p.owner = nru } and
        no { t: Trip | t.owner = nru } and
        no { p: Path | p in nru.favoritePaths }
}

// A RegisteredUser can only have paths and trips that they own
fact UsersCanOnlyHaveTheirOwnPathsAndTrips {
    all ru: RegisteredUser | 
        ru.paths in { p: Path | p.owner = ru } and
        ru.trips in { t: Trip | t.owner = ru }
}

// Ensure that paths owned by RegisteredUsers are either public or private
fact PathVisibility {
    all p: Path | p.visibility = Private or p.visibility = Public
}

// A RegisteredUser cannot put their own paths in their favorites
fact OwnerCannotPutOwnPathInFavorites {
    all ru: RegisteredUser |
        no p: ru.favoritePaths | p.owner = ru
}

// Ensure that RegisteredUsers can favorite only public paths
fact RegisteredUsersCanOnlyFavoritePublicPaths {
    all ru: RegisteredUser | 
        all p: ru.favoritePaths | p.visibility = Public
}

// Ensure that if there is at least a path or a trip, there is at least one RegisteredUser
fact AtLeastOneRegisteredUserIfPathsOrTripsExist {
    (some Path or some Trip) implies some RegisteredUser
}