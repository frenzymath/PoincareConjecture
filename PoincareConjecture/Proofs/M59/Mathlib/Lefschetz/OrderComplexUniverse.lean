import PoincareConjecture.Proofs.M02.Topology.FiniteOrderComplex












set_option autoImplicit false

open scoped BigOperators

universe u v w

namespace PoincareConjecture.Proofs.M59

open M02.Topology

variable {J : Type u} {K : Type v} [PartialOrder J] [PartialOrder K]
  [Fintype J] [Fintype K]



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



@[simp] theorem orderComplexHomeomorph_apply (e : J ≃o K)
    (z : (finiteOrderComplex J).space) (k : K) :
    (orderComplexHomeomorph e z).val k = z.val (e.symm k) := rfl




noncomputable def orderComplexULiftHomeomorph (J : Type u) [PartialOrder J] [Fintype J] :
    (finiteOrderComplex (ULift.{w} J)).space ≃ₜ (finiteOrderComplex J).space :=
  orderComplexHomeomorph ULift.orderIso

end PoincareConjecture.Proofs.M59
