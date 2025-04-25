---------------------- MODULE photo_album_current ----------------------
(*
This spec describes a photo album where photos can be added or removed and a
message is sent to a queue for an asynchronous worker to compute the number of
photos and persist it somewhere.

This spec is intended to demonstrate a race in the following case:
A photo gets added
Worker 1 computes the number of photos
A photo gets removed
Worker 2 computes the number of photos
Worker 2 saves the number of photos
Worker 1 saves the (stale) number of photos
Nothing else happens
*)
EXTENDS Naturals, FiniteSets

CONSTANTS PHOTOS, NUM_ACTORS

ASSUME Cardinality(PHOTOS) > 0
ASSUME NUM_ACTORS > 0

VARIABLES
    photos,
    num_photos,
    \* use a counter to represent a message on a queue, since the message contents
    \* don't matter and the order of messages should be irrelevant.
    msg_counter,
    max_changes,
    computed_num_photos,
    pc

--------------------------------------------------------------
vars == <<photos, num_photos, msg_counter, max_changes, computed_num_photos, pc>>
---------------------------------------------------------------
TypeInvariant ==
    /\ photos \in [PHOTOS -> [created: BOOLEAN]]
    /\ num_photos \in Nat
    /\ msg_counter \in Nat
    /\ max_changes \in Nat
    /\ computed_num_photos \in [1..NUM_ACTORS -> Nat]
    /\ pc \in [1..NUM_ACTORS -> {"", "SaveNumPhotos"}]

NumPhotosIsEventuallyCorrect ==
    <>[](num_photos = Cardinality({a \in DOMAIN photos: photos[a].created}))
------------------------------------------------------------------
AddPhoto(pid) ==
    /\ max_changes > 0
    /\ photos[pid].created = FALSE
    /\ photos' = [photos EXCEPT ![pid]["created"] = TRUE]
    /\ msg_counter' = msg_counter + 1
    /\ max_changes' = max_changes - 1
    /\ UNCHANGED <<num_photos, pc, computed_num_photos>>

RemovePhoto(pid) ==
    /\ max_changes > 0
    /\ photos[pid].created = TRUE
    /\ photos' = [photos EXCEPT ![pid]["created"] = FALSE]
    /\ msg_counter' = msg_counter + 1
    /\ max_changes' = max_changes - 1
    /\ UNCHANGED <<num_photos, pc, computed_num_photos>>

\* The number of photos is a proxy for a much more complex computation that
\* computes several statistics, can take a while to compute, and needs
\* to eventually be correct.
ComputeNumPhotos(t) ==
    /\ pc[t] = ""
    /\ msg_counter > 0
    /\ computed_num_photos' = [computed_num_photos EXCEPT ![t] = Cardinality({a \in DOMAIN photos: photos[a].created})]
    /\ pc' = [pc EXCEPT ![t] = "SaveNumPhotos"]
    /\ msg_counter' = msg_counter - 1
    /\ UNCHANGED <<photos, num_photos, max_changes>>

SaveNumPhotos(t) ==
    /\ pc[t] = "SaveNumPhotos"
    /\ num_photos' = computed_num_photos[t]
    /\ pc' = [pc EXCEPT ![t] = ""]
    /\ computed_num_photos' = [computed_num_photos EXCEPT ![t] = 0]
    /\ UNCHANGED <<photos, msg_counter, max_changes>>

---------------------------------------------------------------------------------
Init == /\ msg_counter = 0
        /\ num_photos = 0
        /\ pc = [t \in 1..NUM_ACTORS |-> ""]
        /\ max_changes = 2
        /\ photos = [pid \in PHOTOS |-> [created |-> FALSE]]
        /\ computed_num_photos = [t \in 1..NUM_ACTORS |-> 0]

Next == \/ \E pid \in PHOTOS:
              \/ AddPhoto(pid)
              \/ RemovePhoto(pid)
        \/ \E t \in 1..NUM_ACTORS:
              \/ ComputeNumPhotos(t)
              \/ SaveNumPhotos(t)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
=====================================================
