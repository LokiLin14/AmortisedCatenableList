inductive DebitList where
  | Nil : DebitList
  | Cons : Nat -> List DebitList -> DebitList
  | AmortiseFail : DebitList -> DebitList
deriving Repr, Hashable, BEq

namespace DebitList


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
        let (cls', res) := goList cls (i + 1, depth + 1, acc + n)
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

def cons (cat : DebitList) : DebitList :=
  match cat with
  | Nil => Cons 0 []
  | cl@(Cons _ []) => Cons 0 [cl]
  | cl@(Cons _ _) => Cons 0 [chargeDebit cl]
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

def getShape : (dl : DebitList) -> DebitList
  | Nil => Nil
  | dl@(AmortiseFail _) => dl
  | Cons _ cls => Cons 0 (cls.map getShape)

end DebitList
