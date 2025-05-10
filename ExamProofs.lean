-- This module serves as the root of the `ExamProofs` library.
-- Import modules here that should be built as part of the library.
import ExamProofs.Basic

inductive CatList where
  | Nil : CatList
  | Cons : Nat -> List CatList -> CatList
deriving Repr

namespace CatList

def cons (n : Nat) (cat : CatList) : (CatList × Nat) :=
  match cat with
  | Nil => (Cons n [], 1)
  | cl@(Cons _ _) => (Cons n [cl], 1)

def snoc (cat : CatList) (n : Nat) : (CatList × Nat) :=
  match cat with
  | Nil => (Cons n [], 1)
  | Cons n' cls => (Cons n' (cls ++ [Cons n []]), 1)

def append (cl1 cl2 : CatList) : (CatList × Nat) :=
  match (cl1, cl2) with
  | (Nil, _) => (cl2, 1)
  | (_, Nil) => (cl1, 1)
  | (Cons n cl1', _) => (Cons n (cl1' ++ [cl2]), 1)

def tail (cat : CatList) : (CatList × Nat) :=
  match cat with
  | Nil => (Nil, 1)
  | Cons _ cls =>
    List.foldr
      (fun cl (acc : CatList × Nat) =>
        let (res1, n1) := append cl acc.1
        (res1, n1 + acc.2))
      (Nil, 0)
      cls

def cons' (n: Nat) (cat : CatList) : CatList :=
  (cons n cat).1

def snoc' (cat : CatList) (n: Nat)  : CatList :=
  (snoc cat n).1

-- consMade
def consMade := cons' 1 (cons' 2 (cons' 3 (cons' 4 Nil)))
#eval consMade
#eval tail consMade

-- snocMade
def snocMade := snoc' (snoc' (snoc' (snoc' Nil 1) 2) 3) 4
#eval snocMade
#eval tail snocMade

end CatList
