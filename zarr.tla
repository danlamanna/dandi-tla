---------------------- MODULE zarr ----------------------
(*
This spec models the lifecycle of a Zarr archive, from creation to ingestion.
It constrains the valid state transitions and ensures there are no lost updates.

It's updated to dandi-archive 83d0c44e.
*)
EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANTS ZARRS, NUM_ACTORS, NULL

ASSUME Cardinality(ZARRS) > 0
ASSUME NUM_ACTORS > 0

VARIABLES
    zarrs,
    ram,
    pc,
    \* keep the model running in a reasonable time
    bounded_actions

ZarrStates == {"none", "pending", "uploaded", "ingesting", "complete"}
--------------------------------------------------------------
vars == <<zarrs, bounded_actions, ram, pc>>
---------------------------------------------------------------
RevisionFieldIsMonotonicallyIncreasing(record) ==
    /\ record'.rev = record.rev \/ record'.rev = record.rev + 1

TypeInvariant ==
    /\ \A zid \in ZARRS:
        /\ zarrs[zid].status \in ZarrStates
        /\ zarrs[zid].rev \in Nat
        /\ zarrs[zid].rev >= 0

ZarrStateTransitions == [][
    \A zid \in ZARRS:
        /\ RevisionFieldIsMonotonicallyIncreasing(zarrs[zid])
        /\ zarrs[zid].status # zarrs[zid]'.status => zarrs[zid]'.rev = zarrs[zid].rev + 1

        /\ zarrs[zid].status = "none" => zarrs[zid]'.status \in {"none", "pending"}
        /\ zarrs[zid].status = "pending" => zarrs[zid]'.status \in {"pending", "uploaded"}
        /\ zarrs[zid].status = "uploaded" => zarrs[zid]'.status \in {"ingesting", "uploaded"}
        /\ zarrs[zid].status = "ingesting" => zarrs[zid]'.status \in {"ingesting", "complete"}
        /\ zarrs[zid].status = "complete" => zarrs[zid]'.status \in {"complete", "pending"}
]_zarrs


(*
The way this works is maybe hacky, I think. The transitions from complete -> pending are
under bounded_actions, so they can only happen a finite amount of times. But the actions going
from uploaded -> complete are unbounded, so it's always possible to get to complete and stay
there.
*)
ZarrProcessed == [](\A zid \in ZARRS:
                        zarrs[zid].status = "uploaded" ~> zarrs[zid].status = "complete")
------------------------------------------------------------------
CreateZarrArchive(zid) ==
    /\ zarrs[zid].status = "none"
    /\ zarrs' = [zarrs EXCEPT ![zid]["status"] = "pending",
                              ![zid]["rev"] = @ + 1]
    /\ UNCHANGED <<ram, bounded_actions, pc>>

RequestSignedUrls(zid) ==
    /\ ~zarrs[zid].status \in {"none", "ingesting", "uploaded"}
    /\ bounded_actions.request_urls > 0
    /\ zarrs' = [zarrs EXCEPT ![zid]["status"] = "pending",
                              ![zid]["rev"] = @ + 1]
    /\ bounded_actions' = [bounded_actions EXCEPT !.request_urls = @ - 1]
    /\ UNCHANGED <<ram, pc>>

DeleteZarrFiles(zid) ==
    /\ ~zarrs[zid].status \in {"none", "ingesting", "uploaded"}
    /\ bounded_actions.deletes > 0
    /\ zarrs' = [zarrs EXCEPT ![zid]["status"] = "pending",
                              ![zid]["rev"] = @ + 1]
    /\ bounded_actions' = [bounded_actions EXCEPT !.deletes = @ - 1]
    /\ UNCHANGED <<ram, pc>>

FinalizeZarrArchive(zid) ==
    /\ zarrs[zid].status # "none"
    /\ zarrs[zid].status = "pending"
    /\ zarrs' = [zarrs EXCEPT ![zid]["status"] = "uploaded",
                              ![zid]["rev"] = @ + 1]
    /\ UNCHANGED <<ram, bounded_actions, pc>>

\* TODO: model the force parameter
IngestZarrArchivePart1(t, zid) ==
    /\ zarrs[zid].status # "none"
    /\ pc[t] = NULL
    /\ zarrs[zid].status = "uploaded"
    /\ zarrs' = [zarrs EXCEPT ![zid]["status"] = "ingesting",
                              ![zid]["rev"] = @ + 1]
    /\ pc' = [pc EXCEPT ![t] = "part2"]
    /\ ram' = [ram EXCEPT ![t] = zid]
    /\ UNCHANGED <<bounded_actions>>

IngestZarrArchivePart2(t) ==
    /\ pc[t] = "part2"
    /\ zarrs[ram[t]].status = "ingesting"
    /\ zarrs' = [zarrs EXCEPT ![ram[t]]["status"] = "complete",
                              ![ram[t]]["rev"] = @ + 1]
    /\ ram' = [ram EXCEPT ![t] = NULL]
    /\ pc' = [pc EXCEPT ![t] = NULL]
    /\ UNCHANGED <<bounded_actions>>
---------------------------------------------------------------------------------
Init == /\ ram = [t \in 1..NUM_ACTORS |-> NULL]
        /\ pc = [t \in 1..NUM_ACTORS |-> NULL]
        /\ bounded_actions = [request_urls |-> 4, deletes |-> 4]
        /\ zarrs = [zid \in ZARRS |-> [status |-> "none", rev |-> 0]]

Next == \/ \E t \in 1..NUM_ACTORS:
              \E zid \in ZARRS:
                 \/ CreateZarrArchive(zid)
                 \/ RequestSignedUrls(zid)
                 \/ FinalizeZarrArchive(zid)
                 \/ DeleteZarrFiles(zid)
                 \/ IngestZarrArchivePart1(t, zid)
                 \/ IngestZarrArchivePart2(t)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
=====================================================
