CoInductive itree {Event : Type -> Type} {Result : Type} :=
| Ret : Result -> itree
| Tau : itree -> itree
| Vis : forall {Answer : Type}, Event Answer -> (Answer -> itree) -> itree.

Check itree.
Compute itree.
Compute Ret.
Compute Tau.
Compute Vis.

Inductive IO : Type -> Type :=
| Input : IO nat
| Output : forall (x : nat), IO False.

CoFixpoint echo : @itree IO False :=
  Vis Input (fun (x : nat) =>
  Vis (Output x) (fun y => 
  echo)).

Notation "x <- t1 ;; t2" := (bind t1 (fun x => t2)).


Compute echo.