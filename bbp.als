// ===========================================
// SIGNATURES
// ===========================================

abstract sig User {}

sig NonRegisteredUser extends User {}

sig RegisteredUser extends User {
    email: one String,
    password: one String,
    var verification: one VerificationStatus,
    var paths: set Path,
    var trips: set Trip,
    var favoritePaths: set Path
}

sig Path {
    owner: one RegisteredUser,
    var approval: lone ApprovalStatus,
    var visibility: one Visibility
}

sig Trip {
    owner: one RegisteredUser,
    var recordingState: one RecordingState, 
    followedPath: lone Path
}

sig Report {
    reportedPath: one Path,
    reporter: one RegisteredUser,
    var approval: lone ApprovalStatus
}

enum VerificationStatus { Verified, Unverified }

enum ApprovalStatus { Accepted, Rejected }

enum Visibility { Private, Public }

enum RecordingState { Recording, Paused, Ended }


// ===========================================
// FACTS
// ===========================================

// Ensure unique emails for registered users
fact UniqueEmails {
    all ru1, ru2: RegisteredUser | 
        ru1 != ru2 implies ru1.email != ru2.email
}

// Ensure that registered users and non-registered users are disjoint sets
fact DisjointUsers {
    no RegisteredUser & NonRegisteredUser
}

// Ensure registered user verification status evolution
fact UserVerificationStatusEvolution {

    // Initially, registered user is unverified
    always all ru: RegisteredUser |
        once (ru.verification = Unverified)

    // If a user is verified, it must have been unverified before
    always all ru: RegisteredUser | 
        ru.verification = Verified implies once (ru.verification = Unverified)

    // Once a user is verified, it must remain verified
    always all ru: RegisteredUser | 
        ru.verification = Verified implies after (ru.verification = Verified)
}

// Ensure registered user paths evoulution
fact RegisteredUserPathsEvolution { 

    // Initially, registered user has no paths
    always all ru: RegisteredUser |
        once (no ru.paths)

    // Paths can only be added if they are owned by the user
    always all ru: RegisteredUser |
        all p: ru.paths | p.owner = ru
}

// Ensure registered user trips evolution
fact RegisteredUserTripsEvolution { 

    // Initially, registered user has no trips
    always all ru: RegisteredUser |
        once (no ru.trips)

    // Trips can only be added if they are owned by the user
    always all ru: RegisteredUser |
        all t: ru.trips | t.owner = ru
}

// Ensure registered user favorite paths evolution
fact RegisteredUserFavoritePathsEvolution { 

    // Initially, registered user has no favorite paths
    always all ru: RegisteredUser |
        once (no ru.favoritePaths)

    // Favorite paths can only be added if they are public
    always all ru: RegisteredUser |
        all p: ru.favoritePaths | p.visibility = Public

    // Favorite paths cannot be owned by the user
    always all ru: RegisteredUser |
        all p: ru.favoritePaths | p.owner != ru
}

// Ensure that non-registered users do not have paths, trips, or favorite paths
fact NonRegisteredUsersHaveNothingAssociated {
    all nru: NonRegisteredUser |
        no { p: Path | p.owner = nru } and
        no { t: Trip | t.owner = nru } and
        no { p: Path | p in nru.favoritePaths }
}

// Ensure valid evolution of path lifecycle
fact PathLifecycle {

    // Initially the path is private and there is no approval
    always all p: Path |
        once (p.visibility = Private and no p.approval)

    // If approval is Rejected, visibility must always stay Private
    always all p: Path |
        (p.approval = Rejected implies always (p.visibility = Private))

    // If approval is still not present, visibility must always stay Private
    always all p: Path |
        (no p.approval implies always (p.visibility = Private))

    // If approval is Accepted, visibility can change to Public only after approval
    always all p: Path |
        (p.approval = Accepted implies after (p.visibility = Private or p.visibility = Public))

    // Once a path is Accepted, it must remain Accepted
    always all p: Path |
        (p.approval = Accepted implies after always (p.approval = Accepted))

    // If a path is Public, it has to be Accepted
    always all p: Path |
        (p.visibility = Public implies p.approval = Accepted)
}

// Ensure that trips are related only to path that are owned by the trip owner or public paths
fact TripPathsOwnershipOrPublic {
    all t: Trip | 
        all p: t.followedPath | 
            p.owner = t.owner or p.visibility = Public
}

// Ensure valid evolution of trip recording states
fact TripRecordingStateEvolution {

    // Initially, the trip is in Recording state
    always all t: Trip |
        once (t.recordingState = Recording)

    // Paused has to come from Recording
    always all t: Trip |
        (t.recordingState = Paused implies once (t.recordingState = Recording and t.recordingState' = Paused))

    // Ended has to come from Recording or Paused
    always all t: Trip |
        (t.recordingState = Ended implies once ((t.recordingState = Recording or t.recordingState = Paused) and t.recordingState' = Ended))

    // From Paused, it is possible to return to Recording or go to Ended
    always all t: Trip |
        (t.recordingState = Paused implies t.recordingState' in Recording + Ended)

    // Once Ended, it is not possible to go back
    always all t: Trip |
        (t.recordingState = Ended implies after always (t.recordingState != Recording and t.recordingState != Paused))
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

// Ensure valid evolution of report approval status
fact ReportApprovalStatusEvolution {

    // Initially, approval is absent
    always all r: Report | 
        once (r.approval = none)

    // If approval exists, it must have been none before
    always all r: Report |
        (r.approval in ApprovalStatus implies once (r.approval = none and r.approval' in ApprovalStatus))
}

// Ensure that if there is at least a path or a trip, there is at least one registered user
fact AtLeastOneRegisteredUserIfPathsOrTripsExist {
    (some Path or some Trip) implies some RegisteredUser
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
fun availablePath[ru: RegisteredUser]: set Path {
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