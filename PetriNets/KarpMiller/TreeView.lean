/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.KarpMiller

/-!
# Rendering Karp–Miller trees

This convenience module provides printable and Graphviz DOT views of finite
Karp–Miller trees. It is separate from the construction and its proofs: users
who only need the formalised algorithm do not need to import the rendering
code.
-/

@[expose] public section

namespace PetriNet.KarpMiller

variable {P T : Type*}
variable [FinEnum P]

/-- A printable view of a Karp–Miller tree.

Markings are functions and therefore cannot be printed directly. This view
replaces each marking by the finite list of its place/value pairs and omits
the ancestor history stored internally by the algorithm. -/
inductive KarpMillerTree.View (P T : Type*) where
  | node (marking : List (P × String))
      (children : List (T × KarpMillerTree.View P T))
  deriving Repr

/-- Render a token count, using `ω` for the top element. -/
def omegaValueToString (n : ℕ∞) : String :=
  if n = ⊤ then "ω" else toString (n.untopD 0)

mutual
  /-- Convert a Karp–Miller tree to its printable view. -/
  def KarpMillerTree.toView :
      KarpMillerTree P T → KarpMillerTree.View P T
    | .node rootValue children =>
        .node
          ((FinEnum.toList P).map fun p =>
            (p, omegaValueToString (rootValue.marking p)))
          (KarpMillerTree.childrenToViews children)

  /-- Convert a list of labelled child trees to printable views. -/
  def KarpMillerTree.childrenToViews :
      List (T × KarpMillerTree P T) →
        List (T × KarpMillerTree.View P T)
    | [] => []
    | (t, tree) :: children =>
        (t, tree.toView) :: KarpMillerTree.childrenToViews children
end

/-- Render the marking at a tree node as a DOT label, with one place per line. -/
def KarpMillerTree.markingDotLabel [ToString P] (node : KarpMillerNode P) : String :=
  String.intercalate "\\n" <|
    (FinEnum.toList P).map fun p =>
      s!"{toString p} = {omegaValueToString (node.marking p)}"

mutual
  /-- Generate the DOT statements for a tree and return the next unused node
  identifier. -/
  def KarpMillerTree.toDotLines [ToString P] [ToString T]
      (tree : KarpMillerTree P T) (id : ℕ) : ℕ × List String :=
    match tree with
    | .node rootValue children =>
        let nodeLine :=
          s!"  n{id} [label=\"{KarpMillerTree.markingDotLabel rootValue}\"];"
        let result := KarpMillerTree.childrenToDotLines children id (id + 1)
        (result.1, nodeLine :: result.2)

  /-- Generate DOT edges and subtrees for a list of labelled children. -/
  def KarpMillerTree.childrenToDotLines [ToString P] [ToString T]
      (children : List (T × KarpMillerTree P T))
      (parentId nextId : ℕ) : ℕ × List String :=
    match children with
    | [] => (nextId, [])
    | (t, tree) :: rest =>
        let childId := nextId
        let childResult := tree.toDotLines childId
        let restResult :=
          KarpMillerTree.childrenToDotLines rest parentId childResult.1
        let edgeLine :=
          s!"  n{parentId} -> n{childId} [label=\"{toString t}\"];"
        (restResult.1, edgeLine :: childResult.2 ++ restResult.2)
end

/-- Export a finite Karp–Miller tree in Graphviz DOT format. -/
def KarpMillerTree.toDot [ToString P] [ToString T]
    (tree : KarpMillerTree P T) : String :=
  let lines := (tree.toDotLines 0).2
  String.intercalate "\n" <|
    ["digraph KarpMiller {", "  rankdir=LR;", "  node [shape=box];"] ++
      lines ++ ["}"]

end PetriNet.KarpMiller
