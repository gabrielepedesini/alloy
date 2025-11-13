// ===========================================
// SIGNATURES
// ===========================================

abstract sig User {}

sig NonRegisteredUser extends User {}

sig RegisteredUser extends User {
    email: one String,
    password: one String,
    verification: one VerificationStatus,
    paths: set Path,
    trips: set Trip,
    favoritePaths: set Path
}

sig Path {
    owner: one RegisteredUser,
    approval: lone Status,
    visibility: one Visibility
}

sig Trip {
    owner: one RegisteredUser,
    followedPath: lone Path
}

sig Report {
    reportedPath: one Path,
    reporter: one RegisteredUser,
    approval: lone Status
}

abstract sig VerificationStatus {}
sig Verified, Unverified extends VerificationStatus {}

abstract sig Status {}
sig Accepted, Rejected extends Status {}

abstract sig Visibility {} 
sig Private, Public extends Visibility {}


// ===========================================
// FACTS
// ===========================================

// Ensure unique emails for registered users
fact UniqueEmails {
    all ru1, ru2: RegisteredUser | 
        ru1 != ru2 implies ru1.email != ru2.email
}

// Ensure registered user is unverified or verified
fact ValidVerificationStatus {
    all ru: RegisteredUser | 
        ru.verification = Verified or ru.verification = Unverified
}

// Ensure that a registered user is initially unverified and has no paths or trips
fact InitialUserState {
    all ru: RegisteredUser | 
        ru.verification = Unverified and
        no ru.paths and
        no ru.trips and
        no ru.favoritePaths and 
        no r: Report | r.reporter = ru
}

// Ensure that registered users and non-registered users are disjoint sets
fact DisjointUsers {
    no RegisteredUser & NonRegisteredUser
}

// Ensure that non-registered users do not have paths, trips, or favorite paths
fact NonRegisteredUsersHaveNothingAssociated {
    all nru: NonRegisteredUser |
        no { p: Path | p.owner = nru } and
        no { t: Trip | t.owner = nru } and
        no { p: Path | p in nru.favoritePaths }
}

// A registered user can only have paths and trips that they own
fact UsersCanOnlyHaveTheirOwnPathsAndTrips {
    all ru: RegisteredUser | 
        ru.paths in { p: Path | p.owner = ru } and
        ru.trips in { t: Trip | t.owner = ru }
}

// Ensure that paths owned by registered users are either public or private
fact PathVisibility {
    all p: Path | p.visibility = Private or p.visibility = Public
}

// Ensure that a path can be public only after being accepted
fact PublicPathsMustBeAccepted {
    all p: Path | 
        p.visibility = Public implies p.approval = Accepted
}

// A registered user cannot put their own paths in their favorites
fact OwnerCannotPutOwnPathInFavorites {
    all ru: RegisteredUser |
        no p: ru.favoritePaths | p.owner = ru
}

// Ensure that registered users can favorite only public paths
fact RegisteredUsersCanOnlyFavoritePublicPaths {
    all ru: RegisteredUser | 
        all p: ru.favoritePaths | p.visibility = Public
}

// Ensure that trips are related only to path that are owned by the trip owner or public paths
fact TripPathsOwnershipOrPublic {
    all t: Trip | 
        all p: t.followedPath | 
            p.owner = t.owner or p.visibility = Public
}

// Ensure that if there is at least a path or a trip, there is at least one registered user
fact AtLeastOneRegisteredUserIfPathsOrTripsExist {
    (some Path or some Trip) implies some RegisteredUser
}

// Ensure a report is created by a registered user for a path that he does not own
fact ReportCreation {
    all r: Report | 
        r.reporter != r.reportedPath.owner
}

// Ensure that report is related to a public path
fact ReportedPathIsPublic {
    all r: Report | r.reportedPath.visibility = Public
}

// Ensure that reports that are create eventually get accepted or rejected
fact EachReportEventuallyGetsStatus {
    all r: Report | 
        (no r.approval) implies eventually some r.approval
}


// ===========================================
// PREDICATES
// ===========================================


// A new registered user is created and verified
pred RegisterUser[ru: RegisteredUser] {
    ru.verification = Unverified
    no ru.paths and no ru.trips
}

// A registered user becomes verified after email confirmation
pred VerifyUser[ru: RegisteredUser] {
    ru.verification = Verified
}

// A registered user records a trip
pred RecordTrip[ru: RegisteredUser, t: Trip] {
    t.owner = ru
    t.followedPath = none or t.followedPath.visibility = Public or t.followedPath.owner = ru
}

// A registered user creates a new path (still not approved)
pred CreatePath [ru: RegisteredUser, p: Path] {
    p.owner = ru
    p.visibility = Private
    p.approval = none
    p in ru.paths
}

// The system accepts a path for publication
pred PublishPath [p: Path] {
    p.approval = Accepted
    p.visibility = Public
}

// The system rejects a path for publication
pred RejectPath [p: Path] {
    p.approval = Rejected
    p.visibility = Private
}

// A registered user publishes a path
pred PublishPath [ru: RegisteredUser, p: Path] {
    p.owner = ru
    p.approval = Accepted
    p.visibility = Public
    p in ru.paths
}

// A registered user adds a path to favorites
pred FavoritePath [ru: RegisteredUser, p: Path] {
    p.owner != ru
    p.visibility = Public
    p in ru.favoritePaths
}

// A registered user reports a problem with a public path
pred ReportPath [ru: RegisteredUser, p: Path, r: Report] {
    p.owner != ru
    p.visibility = Public
    r.reporter = ru
    r.reportedPath = p
}


// ===========================================
// FUNCTIONS
// ===========================================


// All public paths in the system
fun publicPaths: set Path {
    {p: Path | p.visibility = Public}
}

// All private paths in the system
fun privatePaths: set Path {
    {p: Path | p.visibility = Private}
}

// All verified users
fun verifiedUsers: set RegisteredUser {
    {ru: RegisteredUser | ru.verification = Verified}
}

// All paths available to a given user (their own + public)
fun availablePath: set Path {
    {p: Path | p.visibility = Public or p.owner = ru}
}

// All reports awaiting approval
fun waitingReports: set Report {
    {r: Report | r.approval = Accepted}
}

// Paths reported by at least one user
fun reportedPath: set Path {
    {r: Report.reportedPath}
}


// ===========================================
// ASSERTIONS
// ===========================================


// No user can favorite their own path
assert NoSelfFavorite {
    all ru: RegisteredUser | no p: ru.favoritePaths | p.owner = ru
}

// Every public path must be accepted
assert PublicPathsAreAccepted {
    all p: Path | p.visibility = Public implies p.approval = Accepted
}

// Every report refers to a public path
assert ReportsOnPublicPaths {
    all r: Report | r.reportedPath.visibility = Public
}