import PoincareConjecture.Proofs.M76.Mathlib.PolygonRegionRecognition
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Topology.Order.Compact










set_option autoImplicit false

open Set Metric

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem exists_pos_smul_add_mem_of_isOpen {U : Set E} (hU : IsOpen U)
    {x : E} (hx : x ∈ U) (v : E) : ∃ t : ℝ, 0 < t ∧ t • v + x ∈ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hx
  let t := ε / (‖v‖ + 1)
  have hden : 0 < ‖v‖ + 1 := by positivity
  have ht : 0 < t := div_pos hε hden
  have hmul : t * (‖v‖ + 1) = ε := div_mul_cancel₀ ε (ne_of_gt hden)
  refine ⟨t, ht, hball ?_⟩
  change dist (t • v + x) x < ε
  rw [dist_eq_norm, add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  nlinarith





theorem IsOpen.affine_le_on_closure_of_le_frontier [FiniteDimensional ℝ E]
    {U : Set E} (hU : IsOpen U) (hbounded : Bornology.IsBounded U)
    (A : E →ᵃ[ℝ] ℝ) (v : E) (hv : 0 < A.linear v) {a : ℝ}
    (hfront : ∀ x ∈ frontier U, A x ≤ a) : ∀ x ∈ closure U, A x ≤ a := by
  intro x hx
  obtain ⟨y, hy, hmax⟩ := hbounded.isCompact_closure.exists_isMaxOn ⟨x, hx⟩
    A.continuous_of_finiteDimensional.continuousOn
  have hyfront : y ∈ frontier U := by
    refine ⟨hy, ?_⟩
    intro hyint
    obtain ⟨t, ht, htU⟩ := exists_pos_smul_add_mem_of_isOpen hU
      (interior_subset hyint) v
    have hle := hmax (subset_closure htU)
    have hheight : A (t • v + y) = t * A.linear v + A y := by
      simpa only [vadd_eq_add, map_smul, smul_eq_mul] using A.map_vadd y (t • v)
    change A (t • v + y) ≤ A y at hle
    rw [hheight] at hle
    linarith [mul_pos ht hv]
  exact (hmax hx).trans (hfront y hyfront)





theorem IsOpen.eq_empty_of_bounded_frontier_subset_affine_level [FiniteDimensional ℝ E]
    {U : Set E} (hU : IsOpen U) (hbounded : Bornology.IsBounded U)
    (A : E →ᵃ[ℝ] ℝ) (v : E) (hv : 0 < A.linear v) {a : ℝ}
    (hfront : frontier U ⊆ {x | A x = a}) : U = ∅ := by
  have hupper := hU.affine_le_on_closure_of_le_frontier hbounded A v hv
    (fun x hx => le_of_eq (hfront hx))
  have hneg : 0 < (-A).linear (-v) := by simpa using hv
  have hlower := hU.affine_le_on_closure_of_le_frontier hbounded (-A) (-v) hneg
    (a := -a) (fun x hx => by
      change -A x ≤ -a
      rw [hfront hx])
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxheight : A x = a := by
    have h₁ := hupper x (subset_closure hx)
    have h₂ := hlower x (subset_closure hx)
    change -A x ≤ -a at h₂
    linarith
  obtain ⟨t, ht, htU⟩ := exists_pos_smul_add_mem_of_isOpen hU hx v
  have hle := hupper (t • v + x) (subset_closure htU)
  have hheight : A (t • v + x) = t * A.linear v + A x := by
    simpa only [vadd_eq_add, map_smul, smul_eq_mul] using A.map_vadd x (t • v)
  rw [hheight, hxheight] at hle
  linarith [mul_pos ht hv]

end Set
