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

    // Initially, registered user is unverified
    always all ru: RegisteredUser |
        once (ru.verification = Unverified)

    // If a user is verified, it must have been unverified before
    always all ru: RegisteredUser | 
        ru.verification = Verified implies once (ru.verification = Unverified)

    // Once a user is verified, it must remain verified
    always all ru: RegisteredUser | 
        ru.verification = Verified implies after (ru.verification = Verified)

    // Verification can change from Unverified to Verified or stay Unverified
    always all ru: RegisteredUser |
        ru.verification = Unverified implies (ru.verification' = Unverified or ru.verification' = Verified)
}

// Ensure registered user paths evoulution
fact RegisteredUserPathsEvolution { 

    // Initially, registered user has no paths
    always all ru: RegisteredUser |
        once (no ru.paths)

    // Paths can only be added if they are owned by the user
    always all ru: RegisteredUser |
        all p: ru.paths | p.owner = ru

    // Paths can be added to a user's paths
    always all ru: RegisteredUser | 
        all p: Path | 
            (p.owner = ru and p not in ru.paths) implies p in ru.paths'
}

// Ensure registered user trips evolution
fact RegisteredUserTripsEvolution { 

    // Initially, registered user has no trips
    always all ru: RegisteredUser |
        once (no ru.trips)

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

    // Favorite paths can be added
    always all ru: RegisteredUser |
        all p: Path |
            (p.visibility = Public and p.owner != ru and p not in ru.favoritePaths) implies p in ru.favoritePaths'
}

// Ensure valid evolution of path lifecycle
fact PathLifecycle {

    // Initially the path is private and there is no approval
    always all p: Path |
        once (p.visibility = Private and no p.approval)

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
// SIMPLE TESTS
// ===========================================

// Test 1: Just check if initial state is satisfiable
run InitialStateCheck {} for 2 but 2 steps

// Test 2: Simple verification
run SimpleVerification {
    some ru: RegisteredUser | eventually (ru.verification = Verified)
} for 2 but 3 steps

// Test 3: Path approval
run PathApproval {
    some p: Path | eventually p.approval = Accepted
} for 2 but 3 steps

// Test 4: User journey
run UserJourney {
    some ru: RegisteredUser, p: Path | {
        p.owner = ru
        eventually ru.verification = Verified
        eventually p in ru.paths
        eventually p.approval = Accepted
    }
} for 2 but 5 steps

// Test 5: Complete workflow
run CompleteWorkflow {
    some ru: RegisteredUser, p: Path, t: Trip | {
        p.owner = ru
        t.owner = ru
        eventually ru.verification = Verified
        eventually p in ru.paths
        eventually p.approval = Accepted
    }
} for 2 but 5 steps

// Test 6: Multi-user path sharing workflow
run MultiUserPathSharing {
    some ru1, ru2: RegisteredUser, p: Path, fav: Path | {
        ru1 != ru2
        p.owner = ru1
        fav.owner = ru1
        eventually ru1.verification = Verified
        eventually ru2.verification = Verified
        eventually p in ru1.paths
        eventually p.approval = Accepted
        eventually p.visibility = Public
        eventually fav in ru1.paths
        eventually fav.approval = Accepted
        eventually fav.visibility = Public
        eventually fav in ru2.favoritePaths
    }
} for 3 but 8 steps

// Test 7: Report workflow with path approval
run ReportWorkflow {
    some ru1, ru2: RegisteredUser, p: Path, r: Report | {
        ru1 != ru2
        p.owner = ru1
        r.reportedPath = p
        r.reporter = ru2
        eventually ru1.verification = Verified
        eventually ru2.verification = Verified
        eventually p in ru1.paths
        eventually p.approval = Accepted
        eventually p.visibility = Public
        eventually r.approval = Accepted
    }
} for 3 but 8 steps

// Test 8: Complete trip lifecycle with state transitions
run CompleteTripsLifecycle {
    some ru: RegisteredUser, t1, t2: Trip | {
        t1 != t2
        t1.owner = ru
        t2.owner = ru
        eventually ru.verification = Verified
        eventually t1 in ru.trips
        eventually t1.recordingState = Paused
        eventually t1.recordingState = Recording
        eventually t1.recordingState = Ended
        eventually t2 in ru.trips
        eventually t2.recordingState = Paused
    }
} for 3 but 10 steps

// Test 9: Multiple paths with mixed approval statuses
run MultiplePathsWithApprovals {
    some ru: RegisteredUser, p1, p2, p3: Path | {
        p1 != p2 and p2 != p3 and p1 != p3
        p1.owner = ru
        p2.owner = ru
        p3.owner = ru
        eventually ru.verification = Verified
        eventually p1 in ru.paths
        eventually p2 in ru.paths
        eventually p3 in ru.paths
        eventually p1.approval = Accepted
        eventually p2.approval = Rejected
        eventually p3.approval = Accepted
        eventually p1.visibility = Public
        eventually p2.visibility = Private
        eventually p3.visibility = Public
    }
} for 3 but 8 steps

// Test 10: Complex scenario - User creates path, others favorite it, reports it
run ComplexMultiUserScenario {
    some creator, favoriter, reporterUser: RegisteredUser, 
        path: Path, rep: Report | {
        creator != favoriter and favoriter != reporterUser and creator != reporterUser
        path.owner = creator
        rep.reportedPath = path
        rep.reporter = reporterUser
        eventually creator.verification = Verified
        eventually favoriter.verification = Verified
        eventually reporterUser.verification = Verified
        eventually path in creator.paths
        eventually path.approval = Accepted
        eventually path.visibility = Public
        eventually path in favoriter.favoritePaths
        eventually rep.approval in ApprovalStatus
    }
} for 4 but 10 steps

// Test 11: Trip lifecycle with path following
run TripWithPathFollowing {
    some ru1, ru2: RegisteredUser, t: Trip, p: Path | {
        ru1 != ru2
        t.owner = ru1
        p.owner = ru2
        t.followedPath = p
        eventually ru1.verification = Verified
        eventually ru2.verification = Verified
        eventually p in ru2.paths
        eventually p.approval = Accepted
        eventually p.visibility = Public
        eventually t in ru1.trips
        eventually t.recordingState = Recording
        eventually t.recordingState = Paused
        eventually t.recordingState = Ended
    }
} for 3 but 10 steps

// Test 12: Unverified users cannot have interactions
run UnverifiedUserRestrictions {
    some ru: RegisteredUser | {
        ru.verification = Unverified
        always (no p: Path | p.owner = ru)
        always (no t: Trip | t.owner = ru)
    }
} for 2 but 4 steps

// Test 13: State persistence - verified users stay verified
run VerificationPersistence {
    some ru: RegisteredUser | {
        eventually ru.verification = Verified
        eventually always (ru.verification = Verified)
    }
} for 2 but 5 steps

// Test 14: Path state machine - from private to public
run PathStateMachine {
    some p: Path | {
        eventually (p.visibility = Private and no p.approval)
        eventually (no p.approval implies p.visibility = Private)
        eventually p.approval = Accepted
        eventually p.visibility = Public
        eventually always (p.approval = Accepted)
    }
} for 2 but 6 steps

// Test 15: Core entities with specific scope
run CoreEntitiesScope {} for 5 but exactly 2 RegisteredUser, exactly 3 Path, exactly 2 Trip, exactly 10 steps

