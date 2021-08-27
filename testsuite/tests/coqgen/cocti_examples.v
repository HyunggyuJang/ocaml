From mathcomp Require Import all_ssreflect.
Require Import Int63 cocti_defs.

Inductive ml_type : Set :=
  | ml_arrow of ml_type & ml_type
  | ml_pair of ml_type & ml_type
  | ml_list of ml_type
  | ml_ref of ml_type
  | ml_int
  | ml_bool
  | ml_empty.
(* | ml_triple of ml_type & ml_type & ml_type. *)

Module MLtypes.
(* Scheme Equality for ml_type. *)
Definition ml_type_eq_dec (T1 T2 : ml_type) : {T1=T2}+{T1<>T2}.
revert T2; induction T1; destruct T2;
  try (right; intro; discriminate); try (now left);
  try (case (IHT1_5 T2_5); [|right; injection; intros; contradiction]);
  try (case (IHT1_4 T2_4); [|right; injection; intros; contradiction]);
  try (case (IHT1_3 T2_3); [|right; injection; intros; contradiction]);
  try (case (IHT1_2 T2_2); [|right; injection; intros; contradiction]);
  (case (IHT1 T2) || case (IHT1_1 T2_1)); try (left; now subst);
    right; injection; intros; contradiction.
Defined.
Print ml_type_eq_dec.
Require Import Extraction.
Extraction ml_type_eq_dec.

Local Definition ml_type := ml_type.
  
Record key := mkkey {key_id : int; key_type : ml_type}.

Variant loc : ml_type -> Type :=
  mkloc : forall k : key, loc (key_type k).

Section with_monad.
Variable M : Type -> Type.
Local Fixpoint coq_type_rec (p : nat) (T : ml_type) : Type :=
  match T with
  | ml_arrow T1 T2 =>
    let p := p.-1 in
    let ct2 := coq_type_rec p T2 in
    coq_type_rec 0 T1 -> if p is 0 then M ct2 else ct2
  | ml_pair T1 T2 => coq_type_rec 0 T1 * coq_type_rec 0 T2
  | ml_list T1 => list (coq_type_rec 0 T1)
  | ml_ref T1 => loc T1
  | ml_int => Int63.int
  | ml_bool => bool
  | ml_empty => empty
  end.
Local Definition coq_type := coq_type_rec 0.
End with_monad.
End MLtypes.
Export MLtypes.

Module REFmonadML := REFmonad (MLtypes).
Export REFmonadML.

Definition coq_type := MLtypes.coq_type M.
Definition coq_type_purary p T :=
  let ct := MLtypes.coq_type_rec M p T in
  if p is 0 then M ct else ct.

(* Test *)
Definition ml_succ : coq_type (ml_arrow ml_int ml_int) := 
  fun n => Ret (Int63.succ n).

Section comparisons.

Definition lexi_compare (cmp1 cmp2 : M comparison) :=
  do x <- cmp1; match x with Eq => cmp2 | _ => Ret x end.

Fixpoint compare_rec (T : ml_type) (h : nat)
  : coq_type T -> coq_type T -> M comparison:=
  if h is h.+1 then 
    match T as T return coq_type T -> coq_type T -> M comparison with
    | ml_int => fun x y => Ret (Int63.compare x y)
    | ml_bool => fun x y => Ret (Bool.compare x y)
    | ml_pair T1 T2 =>
      fun x y =>
        let (x1, x2) := x in
        let (y1, y2) := y in
        lexi_compare (compare_rec T1 h x1 y1) (Delay (compare_rec T2 h x2 y2))
    | ml_list T1 =>
      fun x y =>
        match x, y with
        | nil, nil => Ret Eq
        | nil, _ => Ret Lt
        | _, nil => Ret Gt
        | x::xs, y::ys =>
          lexi_compare (compare_rec T1 h x y)
                       (Delay (compare_rec (ml_list T1) h xs ys))
        end
    | ml_ref T1 =>
      fun l1 l2 =>
        do x <- getref T1 l1; do y <- getref T1 l2; compare_rec T1 h x y
    | ml_arrow _ _ => fun _ _ => Fail
    | ml_empty => fun _ _ => Fail
    end
  else fun _ _ => Fail.

Definition ml_compare := compare_rec.

Definition wrap_compare wrap T h x y : M bool :=
  do c <- compare_rec T h x y; Ret (wrap c).

Definition ml_eq := wrap_compare (fun c => if c is Eq then true else false).
Definition ml_lt := wrap_compare (fun c => if c is Lt then true else false).
Definition ml_gt := wrap_compare (fun c => if c is Gt then true else false).
Definition ml_ge := wrap_compare (fun c => if c is Lt then false else true).
Definition ml_le := wrap_compare (fun c => if c is Gt then false else true).

End comparisons.

(* Tests and examples *)

Eval compute[ml_eq wrap_compare Bind] in ml_eq.

Definition empty_env := mkEnv 0%int63 nil.

(*
#[bypass_check(positivity)]
Inductive Envi := mkEnvi : (Envi -> Envi) -> Envi.

Definition Delta := fun x => let: mkEnvi y := x in y x.
Definition Omega := Delta (mkEnvi Delta).
Eval cbv in Omega.
 *)

(* We can define Omega
   let omega i =
     let r = ref (fun x -> x) in
     let delta i = !r i in
     r := delta; delta i;;
*)
Definition Omega : M empty :=
  do r : loc (ml_arrow ml_int ml_empty)
     <- newref (ml_arrow ml_int ml_empty) (fun x => Fail);
  let Delta i := do f <- getref _ r; f i in
  do _ <- setref _ r Delta; Delta 1%int63.

(* Evaluation loops *)
(* Eval cbv in Omega empty_env. *)
(* Use Scheme Equality, evaluation stops, but this is actually due to
   the opacity of andb_prop *)
Fail Transparent andb_prop.

Definition Fix T1 T2 (F : coq_type (ml_arrow (ml_arrow T1 T2) (ml_arrow T1 T2)))
  : M (coq_type (ml_arrow T1 T2)) :=
  do r <- newref (ml_arrow T1 T2) (fun x => Fail);
  let f x :=  do f <- getref _ r; f x in
  do _ <- setref _ r f; Ret f.

Definition incr (l : loc ml_int) : M int :=
  do x <- getref _ l; do _ <- setref _ l (succ x); Ret (succ x).

Eval compute in (do l <- newref ml_int 3; incr l)%int63 empty_env.

Module Test.
Set Printing Coercions.
Unset Printing Notations.
Print incr.
End Test.

Section examples.

Definition nil_1 :=
  (fun T : ml_type =>
     do x <- newref (ml_list T) (@nil (coq_type T)); getref (ml_list T) x)
    ml_empty
    empty_env.
Eval vm_compute in nil_1.

Definition onel :=
  (do nil_1 <- K nil_1;
   Ret (1%int63 :: cast_list (cast_empty ml_int) nil_1)) empty_env.

Fixpoint fib (h : nat) (n : int) : M int :=
  if h is h.+1 then
    if leb n 1%int63 then Ret 1%int63 else
    (do x <- fib h (n-1); do y <- fib h (n-2); Ret (x + y))%int63
  else Fail.

(*
let rec ack m n =
    if m <= 0 then n + 1 else
    if n <= 0 then ack (m-1) 1 else
    ack (m-1) (ack m (n-1))
*)

Fixpoint ack (h : nat) (m : int) : M (int -> M int) :=
  if h is h.+1 then
    Ret (fun n =>
           if leb m 0 then Ret (succ n) else
           if leb n 0 then do f <- ack h (m-1); f 1 else
           do x <- AppM (ack h m) (n-1); AppM (ack h (m-1)) x)%int63
  else Fail.

Eval native_compute in fib 100 20%int63 empty_env.

Eval native_compute in (AppM (ack 100000 3%int63) 7%int63) empty_env.

Fixpoint iter_int {T} (h : nat) (n : int) (f : T -> M T) (x : T) :=
  if h is h.+1 then
    (if leb n 0 then Ret x else do y <- f x; iter_int h (n-1) f y)%int63
  else Fail.

Definition fib2 h n : M int :=
  (do l1 : loc ml_int <- newref ml_int 1; do l2 : loc ml_int <- newref ml_int 1;
   do _ <- iter_int h n
     (fun _ => do x <- getref _ l1; do y <- getref _ l2;
               do _ <- setref _ l1 y; setref _ l2 (x+y))
     tt;
   getref _ l1)%int63.

Eval vm_compute in fib2 1001 1000%int63 empty_env.

Fixpoint list_mem (T : ml_type) (h : nat) (a : coq_type T)
         (l : coq_type (ml_list T)) : M bool :=
  if h is h.+1 then
    match l with
    | nil => Ret false
    | b :: l => 
      do e <- ml_eq T h a b; if e then Ret true else list_mem T h a l
    end
  else Fail.

Eval vm_compute in
    list_mem ml_int 100 1%int63 (0 :: 1 :: 2 :: nil)%int63 empty_env.

Fixpoint list_map (T U : ml_type) (h : nat) (f : coq_type (ml_arrow T U))
  (l : list (coq_type T)) : M (list (coq_type U)) :=
  if h is h.+1 then
    match l with
    | nil => Ret nil
    | t :: l =>
      do u <- f t; do l' <- list_map T U h f l; Ret (u :: l')
    end
  else Fail.

Eval vm_compute in list_map ml_int ml_int 10 ml_succ [:: 1; 2; 3]%int63
  empty_env.

End examples.

Print Assumptions Env.
