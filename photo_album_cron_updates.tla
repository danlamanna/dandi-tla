---------------------- MODULE photo_album_cron_updates ----------------------
(*
This spec describes a photo album where photos can be added or removed and a
message is sent to a queue for an asynchronous worker to compute the number of
photos and persist it somewhere.

This spec is intended to demonstrate that recomputing the number of photos
with an optimistic lock on an interval based on whether or not the last modification
occurred after the last summary did.
*)
EXTENDS Naturals, FiniteSets

CONSTANTS PHOTOS, NUM_ACTORS

ASSUME Cardinality(PHOTOS) > 0
ASSUME NUM_ACTORS > 0

VARIABLES
    photos,
    num_photos,
    max_changes,
    computed_num_photos,
    pc,
    last_summary_time,
    last_modified_time,
    \* these will store the last_modified_time per actor to ensure there are no lost updates
    optimistic_locks

--------------------------------------------------------------
vars == <<photos, num_photos, max_changes, computed_num_photos, pc, last_modified_time, last_summary_time, optimistic_locks>>
---------------------------------------------------------------
TypeInvariant ==
    /\ photos \in [PHOTOS -> [created: BOOLEAN]]
    /\ num_photos \in Nat
    /\ max_changes \in Nat
    /\ computed_num_photos \in [1..NUM_ACTORS -> Nat]
    /\ pc \in [1..NUM_ACTORS -> {"", "SaveNumPhotos"}]
    /\ last_modified_time \in Nat
    /\ last_summary_time \in Nat
    /\ optimistic_locks \in [1..NUM_ACTORS -> Nat]

NumPhotosIsEventuallyCorrect ==
    <>[](num_photos = Cardinality({a \in DOMAIN photos: photos[a].created}))
------------------------------------------------------------------
AddPhoto(pid) ==
    /\ max_changes > 0
    /\ photos[pid].created = FALSE
    /\ photos' = [photos EXCEPT ![pid]["created"] = TRUE]
    /\ max_changes' = max_changes - 1
    /\ last_modified_time' = last_modified_time + 1
    /\ UNCHANGED <<num_photos, pc, computed_num_photos, optimistic_locks, last_summary_time>>

RemovePhoto(pid) ==
    /\ max_changes > 0
    /\ photos[pid].created = TRUE
    /\ photos' = [photos EXCEPT ![pid]["created"] = FALSE]
    /\ max_changes' = max_changes - 1
    /\ last_modified_time' = last_modified_time + 1
    /\ UNCHANGED <<num_photos, pc, computed_num_photos, optimistic_locks, last_summary_time>>

\* The number of photos is a proxy for a much more complex computation that
\* computes several statistics, can take a while to compute, and needs
\* to eventually be correct.
ComputeNumPhotos(t) ==
    /\ pc[t] = ""
    /\ last_summary_time < last_modified_time
    /\ computed_num_photos' = [computed_num_photos EXCEPT ![t] = Cardinality({a \in DOMAIN photos: photos[a].created})]
    /\ pc' = [pc EXCEPT ![t] = "SaveNumPhotos"]
    /\ optimistic_locks' = [optimistic_locks EXCEPT ![t] = last_modified_time]
    /\ UNCHANGED <<photos, num_photos, max_changes, last_modified_time, last_summary_time>>

SaveNumPhotos(t) ==
    /\ pc[t] = "SaveNumPhotos"
    /\ pc' = [pc EXCEPT ![t] = ""]
    /\ computed_num_photos' = [computed_num_photos EXCEPT ![t] = 0]
    /\ optimistic_locks' = [optimistic_locks EXCEPT ![t] = 0]
    /\ optimistic_locks[t] = last_modified_time => /\ num_photos' = computed_num_photos[t]
                                                   /\ last_summary_time' = last_modified_time
    /\ optimistic_locks[t] /= last_modified_time => /\ UNCHANGED <<num_photos, last_summary_time>>
    /\ UNCHANGED <<photos, max_changes, last_modified_time>>

---------------------------------------------------------------------------------
Init == /\ num_photos = 0
        /\ pc = [t \in 1..NUM_ACTORS |-> ""]
        /\ max_changes = 2
        /\ photos = [pid \in PHOTOS |-> [created |-> FALSE]]
        /\ computed_num_photos = [t \in 1..NUM_ACTORS |-> 0]
        /\ last_modified_time = 0
        /\ last_summary_time = 0
        /\ optimistic_locks = [t \in 1..NUM_ACTORS |-> 0]

Next == \/ \E pid \in PHOTOS:
              \/ AddPhoto(pid)
              \/ RemovePhoto(pid)
        \/ \E t \in 1..NUM_ACTORS:
              \/ ComputeNumPhotos(t)
              \/ SaveNumPhotos(t)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
=====================================================
