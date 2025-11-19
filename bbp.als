// ===========================================
// SIGNATURES
// ===========================================

sig Email {} {
    Email = RegisteredUser.email
}

abstract sig User {}

sig NonRegisteredUser extends User {}

sig RegisteredUser extends User {
    email: one Email,
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

// Ensure registered user verification status evolution
fact UserVerificationStatusEvolution {

    // Once a user is verified, it must remain verified
    always all ru: RegisteredUser | 
        ru.verification = Verified implies after (ru.verification = Verified)

    // Verification can change from Unverified to Verified or stay Unverified
    always all ru: RegisteredUser |
        ru.verification = Unverified implies (ru.verification' = Unverified or ru.verification' = Verified)

    // Some users are verified from the start
    some ru: RegisteredUser | once ru.verification = Verified

    // Some users are not verified from the start
    some ru: RegisteredUser | once ru.verification = Unverified
}

// Ensure registered user paths evoulution
fact RegisteredUserPathsEvolution { 

    // Paths can only be added if they are owned by the user
    always all ru: RegisteredUser |
        all p: ru.paths | p.owner = ru

    // Paths can be added to a user's paths
    always all ru: RegisteredUser | 
        all p: Path | 
            (p.owner = ru and p not in ru.paths) implies p in ru.paths'

    // Only verified users can have paths
    all ru: RegisteredUser | 
        (some ru.paths) implies ru.verification = Verified
}

// Ensure registered user trips evolution
fact RegisteredUserTripsEvolution { 

    // Trips can only be added if they are owned by the user
    always all ru: RegisteredUser |
        all t: ru.trips | t.owner = ru

    // Trips can be added to a user's trips
    always all ru: RegisteredUser |
        all t: Trip |
            (t.owner = ru and t not in ru.trips) implies t in ru.trips'

    // A single registered user cannot have two trips in Recording or Paused state at the same time
    always all ru: RegisteredUser |
        no t1, t2: ru.trips | 
            t1 != t2 and 
            (t1.recordingState = Recording or t1.recordingState = Paused) and 
            (t2.recordingState = Recording or t2.recordingState = Paused)

    // Trip state can only transition through valid states
    always all t: Trip |
        (t.recordingState = Recording implies (t.recordingState' = Recording or t.recordingState' = Paused or t.recordingState' = Ended)) or
        (t.recordingState = Paused implies (t.recordingState' = Paused or t.recordingState' = Recording or t.recordingState' = Ended)) or
        (t.recordingState = Ended implies t.recordingState' = Ended)

    // Only verified users can have trips
    all ru: RegisteredUser | 
        (some ru.trips) implies ru.verification = Verified
}

// Ensure registered user favorite paths evolution
fact RegisteredUserFavoritePathsEvolution { 

    // Favorite paths can only be added if they are public
    always all ru: RegisteredUser |
        all p: ru.favoritePaths | p.visibility = Public

    // Favorite paths cannot be owned by the user
    always all ru: RegisteredUser |
        all p: ru.favoritePaths | p.owner != ru

    // Favorite paths can be added
    always all ru: RegisteredUser |
        all p: Path |
            (p.visibility = Public and p.owner != ru and p not in ru.favoritePaths) implies p in ru.favoritePaths'

    // Only verified users can have favorite paths
    all ru: RegisteredUser | 
        (some ru.favoritePaths) implies ru.verification = Verified
}

// Ensure valid evolution of path lifecycle
fact PathLifecycle {

    // If approval is Rejected, visibility must always stay Private
    always all p: Path |
        (p.approval = Rejected implies always (p.visibility = Private))

    // If a path is Public, it has to be Accepted
    always all p: Path |
        (p.visibility = Public implies p.approval = Accepted)

    // Once a path is Accepted, it must remain Accepted
    always all p: Path |
        (p.approval = Accepted implies after always (p.approval = Accepted))

    // Approval can transition from none to Accepted or Rejected, or stay the same
    always all p: Path |
        (no p.approval) implies (p.approval' = none or p.approval' in ApprovalStatus)

    // Once approval is assigned, it cannot change
    always all p: Path |
        (p.approval in ApprovalStatus) implies after always (p.approval = p.approval)

    // Paths can only be owned by verified users
    all p: Path | p.owner.verification = Verified
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

    // From Recording, can go to Paused or Ended
    always all t: Trip |
        (t.recordingState = Recording implies (t.recordingState' = Recording or t.recordingState' = Paused or t.recordingState' = Ended))

    // From Paused, can go back to Recording or to Ended
    always all t: Trip |
        (t.recordingState = Paused implies (t.recordingState' = Paused or t.recordingState' = Recording or t.recordingState' = Ended))

    // Once Ended, it must remain Ended
    always all t: Trip |
        (t.recordingState = Ended implies after always (t.recordingState = Ended))

    // Trips can only be owned by verified users
    all t: Trip | t.owner.verification = Verified
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

    // Report approval can change from unapproved to Accepted or Rejected
    always all r: Report |
        (no r.approval) implies (r.approval' = none or r.approval' in ApprovalStatus)

    // Reports can only be created by verified users
    all r: Report | r.reporter.verification = Verified
}

// Ensure that if there is at least a path or a trip, there is at least one registered user
fact AtLeastOneRegisteredUserIfPathsOrTripsExist {
    (some Path or some Trip) implies some RegisteredUser
}


// ===========================================
// PREDICATES
// ===========================================

// A new registered user is created
pred RegisterUser[ru: RegisteredUser] {
    ru.verification = Unverified or ru.verification = Verified
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

// Pauses an active trip
pred PauseTrip[ru: RegisteredUser, t: Trip] {
    t.owner = ru
    t.recordingState = Recording
    t.recordingState' = Paused
}

// Resumes a paused trip
pred ResumeTrip[ru: RegisteredUser, t: Trip] {
    t.owner = ru
    t.recordingState = Paused
    t.recordingState' = Recording
}

// Ends a trip from recording or paused state
pred EndTrip[ru: RegisteredUser, t: Trip] {
    t.owner = ru
    (t.recordingState = Recording or t.recordingState = Paused)
    t.recordingState' = Ended
}

// Approves a report
pred ApproveReport[r: Report] {
    r.approval = none
    r.approval' = Accepted
}

// Rejects a report
pred RejectReport[r: Report] {
    r.approval = none
    r.approval' = Rejected
}

// Removes a path from favorites
pred RemoveFavorite[ru: RegisteredUser, p: Path] {
    p in ru.favoritePaths
    p not in ru.favoritePaths'
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
    {r: Report | no r.approval}
}

// Paths reported by at least one user
fun reportedPath: set Path {
    {r: Report.reportedPath}
}

// Trips in Recording or Paused state for a user
fun activeTrips[ru: RegisteredUser]: set Trip {
    {t: ru.trips | t.recordingState = Recording or t.recordingState = Paused}
}

// Reports without approval
fun pendingReports: set Report {
    {r: Report | no r.approval}
}

// Paths owned by a user
fun userOwnedPaths[ru: RegisteredUser]: set Path {
    {p: Path | p.owner = ru}
}

// Paths with at least one report
fun reportedPaths: set Path {
    {p: Path | some r: Report | r.reportedPath = p}
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

// Ensures no user has multiple active trips
assert UniqueActiveTripsPerUser {
    all ru: RegisteredUser | lone activeTrips[ru]
}

// Verified users remain verified
assert VerifiedUsersStayVerified {
    all ru: RegisteredUser | ru.verification = Verified implies always ru.verification = Verified
}

// Private paths have no approval
assert PrivatePathsUnapproved {
    all p: Path | p.visibility = Private implies no p.approval
}

// Ended trips don't change state
assert EndedTripsStayEnded {
    all t: Trip | t.recordingState = Ended implies always t.recordingState = Ended
}

// Reports are only by non-owners
assert ReportsByNonOwners {
    all r: Report | r.reporter != r.reportedPath.owner
}


// ===========================================
// TEST
// ===========================================

run CoreEntitiesScope {} for 5 but exactly 3 RegisteredUser, exactly 3 Path, exactly 2 Trip, exactly 1 Report, exactly 10 steps