import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Compatibility.ThreeManifoldTopology

/-!
# Relabeling finite order-complex realizations

An order equivalence, including a change of universe by ULift, induces the
literal coordinate-permutation homeomorphism of geometric realizations.
This places M02's finite triangulation in the universe of the covering
manifold without replacing any of its geometric maps.
Source: Hatcher, Theorem 2.27, pp. 128-130; the universe compatibility
derivation in tasks/M59/derivations/2026-09-22-universal-cover.md.
-/

set_option autoImplicit false

open scoped BigOperators

universe u v w

namespace PoincareMT.Proofs.M59

open M02.Topology

variable {J : Type u} {K : Type v} [PartialOrder J] [PartialOrder K]
  [Fintype J] [Fintype K]

/-- Relabeling coordinates preserves the actual order-complex realization.
Source: Hatcher, Theorem 2.27, pp. 128-130; M59 universe derivation. -/
theorem orderComplex_reindex_mem (e : J ≃o K) {z : J → ℝ}
    (hz : z ∈ (finiteOrderComplex J).space) :
    (fun k => z (e.symm k)) ∈ (finiteOrderComplex K).space := by
  have h := (finiteOrderComplex_space J z).mp hz
  apply (finiteOrderComplex_space K _).mpr
  refine ⟨fun k => h.1 (e.symm k), ?_, ?_⟩
  · exact (e.symm.toEquiv.sum_comp z).trans h.2.1
  · intro i j hi hj
    rcases h.2.2 (e.symm i) (e.symm j) hi hj with hij | hji
    · exact Or.inl (e.symm.le_iff_le.mp hij)
    · exact Or.inr (e.symm.le_iff_le.mp hji)

/-- Actual coordinate realizations are homeomorphic under every order
equivalence, with independent vertex universes.
Source: Hatcher, Theorem 2.27, pp. 128-130; M59 universe derivation. -/
noncomputable def orderComplexHomeomorph (e : J ≃o K) :
    (finiteOrderComplex J).space ≃ₜ (finiteOrderComplex K).space where
  toFun z := ⟨fun k => z.val (e.symm k), orderComplex_reindex_mem e z.property⟩
  invFun z := ⟨fun j => z.val (e j), orderComplex_reindex_mem e.symm z.property⟩
  left_inv z := by ext j; simp
  right_inv z := by ext k; simp
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun k => (continuous_apply (e.symm k)).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun j => (continuous_apply (e j)).comp continuous_subtype_val

/-- The relabeling map evaluates by the inverse coordinate permutation.
Source: Hatcher, Theorem 2.27, pp. 128-130; M59 universe derivation. -/
@[simp] theorem orderComplexHomeomorph_apply (e : J ≃o K)
    (z : (finiteOrderComplex J).space) (k : K) :
    (orderComplexHomeomorph e z).val k = z.val (e.symm k) := rfl

/-- Raising the vertex universe leaves the coordinate realization
homeomorphic by the literal up/down permutation.
Source: Hatcher, Theorem 2.27, pp. 128-130; M59 universe derivation. -/
noncomputable def orderComplexULiftHomeomorph (J : Type u) [PartialOrder J] [Fintype J] :
    (finiteOrderComplex (ULift.{w} J)).space ≃ₜ (finiteOrderComplex J).space :=
  orderComplexHomeomorph ULift.orderIso

end PoincareMT.Proofs.M59
