import Std.Data.HashMap
import DebitList
open DebitList

inductive DebitOp where
  | consOp : DebitOp
  | snocOp : DebitOp
  | tailOp : DebitOp
deriving Repr

open DebitOp

def randomOp (rng : StdGen) : DebitOp × StdGen :=
  let (num, rng') := stdNext rng
  let op :=
    match num % 3 with
    | 0 => consOp
    | 1 => snocOp
    | _ => tailOp
  (op, rng')

def applyOp (op : DebitOp) (dl : DebitList) : DebitList :=
  match op with
  | consOp => cons dl
  | snocOp => snoc dl
  | tailOp => tail dl

def getShape : (dl : DebitList) -> DebitList
  | Cons _ cls => Cons 0 (cls.map getShape)
  | x => x

structure CollisionTrace where
  numberOfOperations : Nat
  operations : List (DebitOp × DebitList)
  collision : DebitList × DebitList

def findCollision (seed : Nat) : Option (CollisionTrace) := do
  let mut dl := Nil
  let mut rng := mkStdGen seed
  let mut dls : Std.HashMap DebitList (DebitList) := {}
  let mut operations := []

  for currentStep in [1: 1000] do
    let (op, rng') := randomOp rng
    rng := rng'

    operations := (op, dl) :: operations
    dl := applyOp op dl

    let shape := dl.getShape
    match dls[shape]? with
    | none => dls := dls.insert shape dl
    | some x =>
      if x != dl then
        let ct : CollisionTrace := {
          numberOfOperations := currentStep,
          operations := operations,
          collision := (x, dl)
        }
        return ct
  none

def main : IO Unit := do
  let traces : List (Option CollisionTrace) :=
    List.range 1000
      |> List.map fun x => findCollision x
  let maybeBestCollision : Option CollisionTrace :=
    traces.filterMap (fun x => x)
    |> List.foldl
        fun pt ct =>
          match pt with
          | none => some ct
          | some x =>
            if x.numberOfOperations <= ct.numberOfOperations then
              some x
            else
              some ct
        (none : Option CollisionTrace)

  let some bestCollision <- pure maybeBestCollision
    | do
      println! "No collisions found!"
      return

  println! s!"Found collision in {bestCollision.numberOfOperations} operations :("
  for (operation, debitList) in bestCollision.operations.reverse do
    println! s!"Applying operation {repr operation} to {repr debitList}"
  println! s!"Collision: {repr bestCollision.collision.1}"
  println! s!"Collision: {repr bestCollision.collision.2}"
