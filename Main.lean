import Std.Data.HashMap
open Lean

inductive DebitList where
  | Nil : DebitList
  | Cons : Nat -> List DebitList -> DebitList
  | AmortiseFail : DebitList -> DebitList
deriving Repr

open DebitList

def cons (cat : DebitList) : DebitList :=
  match cat with
  | Nil => Cons 0 []
  | cl@(Cons _ _) => Cons 0 [cl]
  | x@(AmortiseFail _) => x

def snoc (cat : DebitList) : DebitList :=
  match cat with
  | Nil => Cons 0 []
  | Cons n' cls => Cons n' (cls ++ [Cons 0 []])
  | x@(AmortiseFail _) => x

def append (cl1 cl2 : DebitList) : DebitList :=
  match (cl1, cl2) with
  | (Nil, _) => cl2
  | (_, Nil) => cl1
  | (Cons n cl1', _) => Cons n (cl1' ++ [cl2])
  | (x@(AmortiseFail _), _) => x

def chargeDebit (cl : DebitList) : DebitList :=
  match cl with
  | Nil => Nil
  | Cons n cls => Cons (n + 1) cls
  | x@(AmortiseFail _) => x

-- does a preorder traversal of the tree and
-- discharges the first debit that causes the inequality D(i) <= i + depth(i) to fail
def dischargeDebit (cl : DebitList) : DebitList :=
  match cl with
  | Nil => Nil
  | x@(AmortiseFail _) => x
  | dl@(Cons _ _) => (go dl (0, 0, 0)).1
  where
    go : DebitList -> (Nat × Nat × Nat) -> (DebitList × Option (Nat × Nat))
    | Nil, (i, _, acc) => (Nil, some (i, acc))
    | AmortiseFail d, (i, _, acc) => (AmortiseFail d, some (i, acc))
    | Cons n cls, (i, depth, acc) =>
      if acc + n > i + depth then (Cons n.pred cls, none)
      else
        let (cls', res) := goList cls (i, depth + 1, acc + n)
        (Cons n cls', res)
    goList : List DebitList -> (Nat × Nat × Nat) -> (List DebitList × Option (Nat × Nat))
    | [], (i, _, acc) => ([], some (i, acc))
    | (cl :: cls), (i, depth, acc) =>
      let (cl', res) := go cl (i, depth, acc)
      match res with
      | none => (cl' :: cls, none)
      | some (i', acc') =>
        let (cls', res') := goList cls (i', depth, acc')
        ((cl' :: cls'), res')

def tail (cat : DebitList) : DebitList :=
  match cat with
  | Nil => Nil
  | Cons 0 cls =>
    cls.mapIdx (fun i x =>
      if i >= 1 && i <= cls.length - 2 then chargeDebit x
      else x)
      |> List.foldr append Nil
      |> dischargeDebit
      |> dischargeDebit
  | cl@(Cons _ _) => AmortiseFail cl
  | x@(AmortiseFail _) => x

def consMade := Nat.repeat cons 5 Nil
-- #eval consMade
-- #eval tail consMade

def snocMade := Nat.repeat snoc 6 Nil
-- #eval snocMade
-- #eval tail snocMade
-- #eval Nat.repeat tail 10 (Nat.repeat snoc 5 (tail snocMade))

def test : IO Nat :=
  return 5

def debitListToString (dl : DebitList) : String :=
  match dl with
  | Nil => s!"Nil"
  | Cons n' cls =>
    let strings := cls.map debitListToString
    s!"Cons {n'} [{strings}]"
  | AmortiseFail f => s!"AmortiseFail {debitListToString f}"

instance : ToString DebitList where
  toString := debitListToString

inductive Op where
  | consOp : Op
  | snocOp : Op
  | tailOp : Op
deriving Repr

def main : IO Unit := do
  for seqLength in [10:30] do
    println! s!"Trying seqLength := {seqLength}"
    for _ in [0 : 100000] do

      let mut dl := Nil
      let mut ops : List Op := []

      for _ in [: seqLength] do
        let opId ← IO.rand 0 2
        let op :=
          match opId with
          | 0 => Op.consOp
          | 1 => Op.snocOp
          | _ => Op.tailOp
        if let (Op.tailOp, Nil) := (op, dl) then
          continue
        dl :=
          match op with
          | Op.consOp => cons dl
          | Op.snocOp => snoc dl
          | Op.tailOp => tail dl
        ops := op :: ops
        if let AmortiseFail _ := dl then
          break

      if let (AmortiseFail _) := dl then
        let sequence : (List (Op × DebitList)) := ops.foldr
          fun op dls =>
            let dl :=
              match dls with
              | [] => Nil
              | List.cons h _ => h
            match op with
            | Op.consOp => cons dl :: dls
            | Op.snocOp => snoc dl :: dls
            | Op.tailOp => tail dl :: dls
          []
          |> List.zip ops
          |> List.reverse
        println! s!"Failed!: "
        println! s!"Ops: {repr sequence}"
        return
