From mathcomp Require Import all_ssreflect.
Require Import Int63 cocti_defs.

Inductive color := | Red | Green | Blue.

Inductive tree (a : Type) (b : Type) :=
  | Leaf (_ : a) : tree a b
  | Node (_ : tree a b) (_ : a) (_ : tree a b) : tree a b.

Inductive ml_type :=
  | ml_int
  | ml_bool
  | ml_unit
  | ml_list (_ : ml_type)
  | ml_color
  | ml_tree (_ : ml_type) (_ : ml_type)
  | ml_ref (_ : ml_type)
  | ml_arrow (_ : ml_type) (_ : ml_type).


Module MLtypes.
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

Local Definition ml_type := ml_type.
Record key := mkkey {key_id : int; key_type : ml_type}.
Variant loc : ml_type -> Type := mkloc : forall k : key, loc (key_type k).

Section with_monad.
Variable M : Type -> Type.
Local
Fixpoint coq_type (T : ml_type) : Type :=
  match T with
  | ml_int => Int63.int
  | ml_bool => bool
  | ml_unit => unit
  | ml_list T1 => list (coq_type T1)
  | ml_color => color
  | ml_tree T1 T2 => tree (coq_type T1) (coq_type T2)
  | ml_ref T1 => loc T1
  | ml_arrow T1 T2 => coq_type T1 -> M (coq_type T2)
  end.

End with_monad.
End MLtypes.
Export MLtypes.

Module REFmonadML := REFmonad (MLtypes).
Export REFmonadML.

Definition coq_type := MLtypes.coq_type M.
Definition empty_env := mkEnv 0%int63 nil.

Fixpoint compare_rec (T : ml_type) (h : nat) :=
  if h is h.+1 then
    match T as T return coq_type T -> coq_type T -> M comparison with
    | ml_int => fun x y => Ret (Int63.compare x y)
    | ml_bool => fun x y => Ret (Bool.compare x y)
    | ml_unit => fun x y => Ret Eq
    | ml_list T1 => fun x y => Fail
    | ml_color => fun x y => Fail
    | ml_tree T1 T2 => fun x y => Fail
    | ml_ref T1 =>
      fun x y =>
        do x <- getref T1 x; do y <- getref T1 y; compare_rec T1 h x y
    | ml_arrow T1 T2 => fun x y => Fail
    end
  else fun _ _ => Fail.

Definition ml_compare := compare_rec.

Definition wrap_compare wrap T h x y : M bool :=
  do c <- compare_rec T h x y; Ret (wrap c).

Definition ml_eq := wrap_compare (fun c => if c is Eq then true else false).
Definition ml_lt := wrap_compare (fun c => if c is Lt then true else false).
Definition ml_gt := wrap_compare (fun c => if c is Gt then true else false).
Definition ml_ne := wrap_compare (fun c => if c is Eq then false else true).
Definition ml_ge := wrap_compare (fun c => if c is Lt then false else true).
Definition ml_le := wrap_compare (fun c => if c is Gt then false else true).

Definition ref' (T : ml_type) := newref T.

Definition id (T : ml_type) (h_1 : coq_type T) : coq_type T := h_1.

Definition incr (r : coq_type (ml_ref ml_int)) : M (coq_type ml_unit) :=
  do x <- getref ml_int r; setref ml_int r (Int63.add x 1%int63).

Eval vm_compute in (do r <- newref ml_int 1%int63; incr r) empty_env.

Fixpoint loop (T T_1 : ml_type) (h : nat) (h_1 : coq_type T_1)
  : M (coq_type T) := if h is h.+1 then loop T T_1 h h_1 else Fail.

Fixpoint fib (h : nat) (n : coq_type ml_int) : M (coq_type ml_int) :=
  if h is h.+1 then
    do v <- ml_le ml_int h n 1%int63;
    if v then Ret 1%int63 else
      do v <- fib h (Int63.sub n 2%int63);
      do v_1 <- fib h (Int63.sub n 1%int63); Ret (Int63.add v_1 v)
  else Fail.

Definition f10 := fib 100000 10%int63 empty_env.

Eval vm_compute in (do f10 <- (fun _ => f10); fib 100000 10%int63) empty_env.

Fixpoint ack (h : nat) (m n : coq_type ml_int) : M (coq_type ml_int) :=
  if h is h.+1 then
    do v <- ml_le ml_int h m 0%int63;
    if v then Ret (Int63.add n 1%int63) else
      do v <- ml_le ml_int h n 0%int63;
      if v then ack h (Int63.sub m 1%int63) 1%int63 else
        do v <- ack h m (Int63.sub n 1%int63); ack h (Int63.sub m 1%int63) v
  else Fail.

Eval vm_compute in
  (do f10 <- (fun _ => f10); ack 100000 3%int63 7%int63) empty_env.

Fixpoint map (T T_1 : ml_type) (h : nat) (f : coq_type (ml_arrow T_1 T))
  (l : coq_type (ml_list T_1)) : M (coq_type (ml_list T)) :=
  if h is h.+1 then
    match l with
    | @nil _ => Ret (@nil (coq_type T))
    | a :: l_1 =>
      do v <- map T T_1 h f l_1;
      do v_1 <- f a; Ret (@cons (coq_type T) v_1 v)
    end
  else Fail.

Eval vm_compute in
  (do f10 <- (fun _ => f10);
   map ml_int ml_int 100000
     (fun x : coq_type ml_int => Ret (Int63.add x 1%int63 : coq_type ml_int))
     (3%int63 :: 2%int63 :: 1%int63 :: @nil (coq_type ml_int)))
    empty_env.

Definition mknode (T : ml_type) (t1 t2 : coq_type (ml_tree ml_int T))
  : coq_type (ml_tree ml_int T) :=
  Node (coq_type ml_int) (coq_type T) t1 0%int63 t2.

Fixpoint iter_int (T : ml_type) (h : nat) (n : coq_type ml_int)
  (f : coq_type (ml_arrow T T)) (x : coq_type T) : M (coq_type T) :=
  if h is h.+1 then
    do v <- ml_lt ml_int h n 1%int63;
    if v then Ret x else do v <- f x; iter_int T h (Int63.sub n 1%int63) f v
  else Fail.

Definition fib2 (h : nat) (n : coq_type ml_int) : M (coq_type ml_int) :=
  do l1 <- newref ml_int 1%int63;
  do l2 <- newref ml_int 1%int63;
  do _ <-
  iter_int ml_unit h n
    (fun _ =>
       do x <- getref ml_int l1;
       do y <- getref ml_int l2;
       do _ <- setref ml_int l1 y; setref ml_int l2 (Int63.add x y))
    tt;
  getref ml_int l1.

Eval vm_compute in
  (do f10 <- (fun _ => f10); fib2 100000 1000%int63) empty_env.

Fixpoint iota (h : nat) (m n : coq_type ml_int)
  : M (coq_type (ml_list ml_int)) :=
  if h is h.+1 then
    do v <- ml_le ml_int h n 0%int63;
    if v then Ret (@nil (coq_type ml_int)) else
      do v <- iota h (Int63.add m 1%int63) (Int63.sub n 1%int63);
      Ret (@cons (coq_type ml_int) m v)
  else Fail.

Eval vm_compute in
  (do f10 <- (fun _ => f10); iota 100000 1%int63 10%int63) empty_env.

Definition omega (T : ml_type) (n : coq_type T) : M (coq_type T) :=
  do r <- newref (ml_arrow T T) (fun x : coq_type T => Ret (x : coq_type T));
  let delta (i : coq_type T) : M (coq_type T) :=
    AppM (getref (ml_arrow T T) r) i
  in do _ <- setref (ml_arrow T T) r delta; delta n.

Definition fixpt (T T_1 : ml_type) (h : nat)
  (f : coq_type (ml_arrow (ml_arrow T_1 T) (ml_arrow T_1 T)))
  : M (coq_type (ml_arrow T_1 T)) :=
  do r <- newref (ml_arrow T_1 T) (fun x : coq_type T_1 => loop T T_1 h x);
  let delta (i : coq_type T_1) : M (coq_type T) :=
    do v <- getref (ml_arrow T_1 T) r; AppM (f v) i
  in do _ <- setref (ml_arrow T_1 T) r delta; Ret delta.

Definition fib_1 :=
  (do f10 <- (fun _ => f10);
   fixpt ml_int ml_int 100000
     (fun fib_1 : coq_type (ml_arrow ml_int ml_int) =>
        Ret
          (fun n : coq_type ml_int =>
             do v <- ml_le ml_int 100000 n 1%int63;
             if v then Ret 1%int63 else
               do v <- fib_1 (Int63.sub n 2%int63);
               do v_1 <- fib_1 (Int63.sub n 1%int63); Ret (Int63.add v_1 v))))
    empty_env.

Eval vm_compute in (do fib_1 <- (fun _ => fib_1); fib_1 10%int63) empty_env.

Definition r :=
  (do fib_1 <- (fun _ => fib_1);
   newref (ml_list ml_int) (3%int63 :: @nil (coq_type ml_int))) empty_env.

Definition z :=
  (do r <- (fun _ => r);
   do _ <-
   (do v <-
    (do v <- getref (ml_list ml_int) r;
     Ret (@cons (coq_type ml_int) 1%int63 v));
    setref (ml_list ml_int) r v);
   getref (ml_list ml_int) r) empty_env.

Eval vm_compute in
  (do r <- (fun _ => r); do z <- (fun _ => z); getref (ml_list ml_int) r)
    empty_env.

Eval vm_compute in (do z <- (fun _ => z); Ret z) empty_env.

Eval vm_compute in
  (do r <- (fun _ => r);
   do z <- (fun _ => z);
   let r_1 := r in
     do _ <-
     (do v <-
      (do v <- getref (ml_list ml_int) r_1;
       Ret (@cons (coq_type ml_int) 1%int63 v));
      setref (ml_list ml_int) r_1 v);
     getref (ml_list ml_int) r_1)
    empty_env.

Fixpoint mccarthy_m (h : nat) (n : coq_type ml_int) : M (coq_type ml_int) :=
  if h is h.+1 then
    do v <- ml_gt ml_int h n 100%int63;
    if v then Ret (Int63.sub n 10%int63) else
      do v <- mccarthy_m h (Int63.add n 11%int63); mccarthy_m h v
  else Fail.

Eval vm_compute in
  (do z <- (fun _ => z); mccarthy_m 100000 10%int63) empty_env.

Fixpoint tarai (h : nat) (x y z_1 : coq_type ml_int) : M (coq_type ml_int) :=
  if h is h.+1 then
    do v <- ml_lt ml_int h y x;
    if v then
      do v <- tarai h (Int63.sub z_1 1%int63) x y;
      do v_1 <- tarai h (Int63.sub y 1%int63) z_1 x;
      do v_2 <- tarai h (Int63.sub x 1%int63) y z_1; tarai h v_2 v_1 v
    else Ret y
  else Fail.

Eval vm_compute in
  (do z <- (fun _ => z); tarai 100000 1%int63 2%int63 3%int63) empty_env.

Eval vm_compute in (do z <- (fun _ => z); omega ml_int 1%int63) empty_env.

Eval vm_compute in
  (do z <- (fun _ => z);
   AppM
     (fixpt ml_unit ml_int 100000
        (fun f : coq_type (ml_arrow ml_int ml_unit) =>
           Ret (f : coq_type (ml_arrow ml_int ml_unit))))
     0%int63)
    empty_env.

