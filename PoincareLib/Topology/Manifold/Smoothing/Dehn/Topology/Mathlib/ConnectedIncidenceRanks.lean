import PoincareLib.Topology.Manifold.Smoothing.Dehn.General.Mathlib.ModTwoCochainIncidence
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Graphs.ComplexCycleLabels
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Ranks of the original connected vertex and edge incidence

The actual graph walks identify the vertex-incidence kernel with the
constant functions. Evaluation at an actual vertex is a linear
equivalence with ZMod 2. Finite rank-nullity then computes the first
two ranks. See Hatcher, Algebraic Topology, pp. 146--147 and 159,
and Dehn derivation 011.
-/

set_option autoImplicit false

open Set
open PreAbstractSimplicialComplex.ModTwoCochains

namespace AbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] (A : AbstractSimplicialComplex ι)

omit [DecidableEq ι] in
/-- A constant value appears twice on every actual edge, so its
vertex incidence vanishes over ZMod 2. See Dehn derivation 011. -/
theorem vertexCoboundary_const (c : ZMod 2) :
    vertexCoboundary A.toPreAbstractSimplicialComplex (fun _ => c) = 0 := by
  classical
  funext e
  rw [vertexCoboundary_apply]
  obtain ⟨i, j, hij, he⟩ := Finset.card_eq_two.mp e.property.2
  rw [he, Finset.sum_pair hij]
  exact CharTwo.add_self_eq_zero c

/-- Vanishing original edge incidence makes a vertex function constant
along every actual graph walk. See Dehn derivation 011. -/
theorem eq_of_mem_vertexCoboundary_ker (hconn : A.edgeGraph.Preconnected)
    {a : ι → ZMod 2}
    (ha : a ∈ LinearMap.ker (vertexCoboundary A.toPreAbstractSimplicialComplex))
    (u v : ι) : a u = a v := by
  have ha' : vertexCoboundary A.toPreAbstractSimplicialComplex a = 0 := ha
  have hedge {i j : ι} (hij : A.edgeGraph.Adj i j) : a i = a j := by
    let e : Edge A.toPreAbstractSimplicialComplex :=
      ⟨{i, j}, hij.2, Finset.card_pair hij.1⟩
    have hz := congrFun ha' e
    rw [vertexCoboundary_apply] at hz
    change (∑ v ∈ ({i, j} : Finset ι), a v) = 0 at hz
    rw [Finset.sum_pair hij.1] at hz
    exact CharTwo.add_eq_zero.mp hz
  obtain ⟨p⟩ := hconn u v
  induction p with
  | nil => rfl
  | cons h _ ih => exact (hedge h).trans ih

/-- Evaluation and the constant function are inverse linear maps on
the actual vertex-incidence kernel. See Dehn derivation 011. -/
noncomputable def vertexCoboundaryKerEquiv (hconn : A.edgeGraph.Preconnected) (v0 : ι) :
    LinearMap.ker (vertexCoboundary A.toPreAbstractSimplicialComplex) ≃ₗ[ZMod 2] ZMod 2 where
  toFun a := a.val v0
  invFun c := ⟨fun _ => c, A.vertexCoboundary_const c⟩
  left_inv a := by
    apply Subtype.ext
    funext v
    exact A.eq_of_mem_vertexCoboundary_ker hconn a.property v0 v
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The original connected graph has exactly one independent constant
vertex cochain, including the single-vertex case. See derivation 011. -/
theorem finrank_ker_vertexCoboundary (hconn : A.edgeGraph.Connected) :
    Module.finrank (ZMod 2)
      (LinearMap.ker (vertexCoboundary A.toPreAbstractSimplicialComplex)) = 1 := by
  let v0 : ι := Classical.choice hconn.nonempty
  simpa using (A.vertexCoboundaryKerEquiv hconn.preconnected v0).finrank_eq

variable [Fintype ι]

/-- Exactness on the actual edge/triangle maps gives their literal
finite rank equation. No Euler identity for a manifold is used.
See Hatcher pp. 146--147 and Dehn derivation 011. -/
theorem edge_incidence_rank_of_exact (hconn : A.edgeGraph.Connected)
    (hexact : LinearMap.ker (edgeCoboundary A.toPreAbstractSimplicialComplex) =
      LinearMap.range (vertexCoboundary A.toPreAbstractSimplicialComplex)) :
    Module.finrank (ZMod 2)
        (LinearMap.range (edgeCoboundary A.toPreAbstractSimplicialComplex)) +
        Nat.card ι = Nat.card (Edge A.toPreAbstractSimplicialComplex) + 1 := by
  classical
  have h0 := (vertexCoboundary A.toPreAbstractSimplicialComplex).finrank_range_add_finrank_ker
  rw [A.finrank_ker_vertexCoboundary hconn, Module.finrank_pi] at h0
  have h1 := (edgeCoboundary A.toPreAbstractSimplicialComplex).finrank_range_add_finrank_ker
  rw [hexact, Module.finrank_pi] at h1
  simp only [Nat.card_eq_fintype_card]
  omega

end AbstractSimplicialComplex
