import PoincareConjecture.Proofs.M36.JetProductBounds
import PoincareConjecture.Proofs.M36.SmoothProfile

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 12

open scoped ContDiff BigOperators Topology

namespace PoincareConjecture.M36

open PoincareConjecture.SpacetimeBounds

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

theorem exists_cylinderCutoff_jet_bounds :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ s ∈ Set.Icc (0 : ℝ) 2, ∀ b : Bool, ∀ k : ℕ, k ≤ 2 →
      ‖iteratedFDeriv ℝ k
        (fun p : E₃ => if b then neckCutoff (cylinderHeightCovector p + s)
          else 1 - neckCutoff (cylinderHeightCovector p + s)) 0‖ ≤ A := by
  classical
  let e := EuclideanSpace.basisFun (Fin 3) ℝ 2
  have he : cylinderHeightCovector e = 1 := by
    dsimp [e]
    rw [cylinderHeightCovector_basis]
    rfl
  let f : Bool → E₃ → ℝ := fun b p =>
    if b then neckCutoff (cylinderHeightCovector p)
      else 1 - neckCutoff (cylinderHeightCovector p)
  have hf (b : Bool) : ContDiff ℝ ∞ (f b) := by
    cases b
    · exact contDiff_const.sub (neckCutoff_contDiff.comp cylinderHeightCovector.contDiff)
    · exact neckCutoff_contDiff.comp cylinderHeightCovector.contDiff
  have hc (a : Bool × Fin 3) : Continuous
      (fun s : ℝ => iteratedFDeriv ℝ (a.2 : ℕ) (f a.1) (s • e)) :=
    ((hf a.1).continuous_iteratedFDeriv
      (by exact_mod_cast (le_top : ((a.2 : ℕ) : ℕ∞) ≤ ⊤))).comp
      (continuous_id.smul continuous_const)
  choose C hC using fun a : Bool × Fin 3 =>
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 2)).exists_bound_of_continuousOn
      (hc a).continuousOn
  let A := 1 + ∑ a : Bool × Fin 3, max (C a) 0
  have hsum : 0 ≤ ∑ a : Bool × Fin 3, max (C a) 0 :=
    Finset.sum_nonneg (fun a _ => le_max_right _ _)
  refine ⟨A, by dsimp [A]; linarith only [hsum], ?_⟩
  intro s hs b k hk
  have heq : (fun p : E₃ => if b then neckCutoff (cylinderHeightCovector p + s)
        else 1 - neckCutoff (cylinderHeightCovector p + s)) =
      fun p => f b (p + s • e) := by
    funext p
    simp only [f, map_add, map_smul, smul_eq_mul, he, mul_one]
  rw [heq, iteratedFDeriv_comp_add_right, zero_add]
  let a : Bool × Fin 3 := (b, ⟨k, by omega⟩)
  have ha : C a ≤ A := by
    calc
      C a ≤ max (C a) 0 := le_max_left _ _
      _ ≤ ∑ j : Bool × Fin 3, max (C j) 0 :=
        Finset.single_le_sum (fun j _ => le_max_right _ _) (Finset.mem_univ a)
      _ ≤ A := by dsimp [A]; linarith
  exact (hC a s hs).trans ha

noncomputable def cylinderBlend (epsilon : ℝ) (H : E₃ → MetricCoefficient 3)
    (s : ℝ) (p : E₃) : MetricCoefficient 3 :=
  neckCutoff (cylinderHeightCovector p + s) • H p +
    (1 - neckCutoff (cylinderHeightCovector p + s)) •
      ((1 - 6 * epsilon) • cylinderModelField p)

theorem cylinderBlend_contDiffAt (epsilon s : ℝ) {H : E₃ → MetricCoefficient 3}
    (hH : ContDiffAt ℝ ∞ H 0) : ContDiffAt ℝ ∞ (cylinderBlend epsilon H s) 0 := by
  have ha : ContDiffAt ℝ ∞ (fun p : E₃ => neckCutoff (cylinderHeightCovector p + s)) 0 :=
    neckCutoff_contDiff.contDiffAt.comp 0
      (cylinderHeightCovector.contDiff.contDiffAt.add contDiffAt_const)
  exact (ha.smul hH).add ((contDiffAt_const.sub ha).smul
    (cylinderModelField_contDiff.contDiffAt.const_smul (1 - 6 * epsilon)))

theorem cylinderBlend_sub_model (epsilon s : ℝ) (H : E₃ → MetricCoefficient 3) :
    (fun p => cylinderBlend epsilon H s p - cylinderModelField p) =
      fun p => neckCutoff (cylinderHeightCovector p + s) • (H p - cylinderModelField p) -
        (6 * epsilon) •
          ((1 - neckCutoff (cylinderHeightCovector p + s)) • cylinderModelField p) := by
  funext p
  unfold cylinderBlend
  module

theorem exists_cylinderBlend_twoJet_bound :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ epsilon : ℝ, 0 < epsilon →
      ∀ B : RoundCylinderTwoTensor, RoundCylinderClose epsilon 0 B →
      2 ≤ ⌊epsilon⁻¹⌋₊ → ∀ z : RoundCylinderSpace,
      z.2 ∈ Set.Icc (0 : ℝ) 2 → z.2 ∈ Set.Ioo (-epsilon⁻¹) epsilon⁻¹ →
      ‖metricTwoJet
          (cylinderBlend epsilon (centeredCylinderMetric B z.1 z.2) z.2) 0 -
        cylinderModelJet‖ ≤ K * epsilon := by
  obtain ⟨A, hA, hcutoff⟩ := exists_cylinderCutoff_jet_bounds
  let M := ‖cylinderModelJet‖
  let K := 4 * A * (810 + 6 * M)
  have hAn : 0 ≤ A := le_trans zero_le_one hA
  have hMn : 0 ≤ M := norm_nonneg _
  refine ⟨max K 1, le_max_right _ _, ?_⟩
  intro epsilon hepsilon B hB horder z hz2 hz
  let H := centeredCylinderMetric B z.1 z.2
  let a : E₃ → ℝ := fun p => neckCutoff (cylinderHeightCovector p + z.2)
  have ha : ContDiffAt ℝ ∞ a 0 := neckCutoff_contDiff.contDiffAt.comp 0
    (cylinderHeightCovector.contDiff.contDiffAt.add contDiffAt_const)
  have hH : ContDiffAt ℝ ∞ H 0 := centeredCylinderMetric_contDiffAt hB z hz
  have hQ := cylinderModelField_contDiff.contDiffAt (x := (0 : E₃))
  have herror : ‖metricTwoJet (fun p => H p - cylinderModelField p) 0‖ ≤
      810 * epsilon := by
    rw [metricTwoJet_sub_of_contDiffAt hH hQ]
    exact roundCylinderClose_twoJet_error hepsilon hB horder z hz
  have haJet : ∀ k : ℕ, k ≤ 2 → ‖iteratedFDeriv ℝ k a 0‖ ≤ A := by
    intro k hk
    simpa [a] using hcutoff z.2 hz2 true k hk
  have hacJet : ∀ k : ℕ, k ≤ 2 →
      ‖iteratedFDeriv ℝ k (fun p => 1 - a p) 0‖ ≤ A := by
    intro k hk
    simpa [a] using hcutoff z.2 hz2 false k hk
  have hfirst := norm_metricTwoJet_smul_le ha (hH.sub hQ) hAn
    (mul_nonneg (by norm_num) hepsilon.le) haJet herror
  have hsecond := norm_metricTwoJet_smul_le (contDiffAt_const.sub ha) hQ hAn hMn
    hacJet (le_refl M)
  have hacQ : ContDiffAt ℝ ∞ (fun p => (1 - a p) • cylinderModelField p) 0 :=
    (contDiffAt_const.sub ha).smul hQ
  have hjet : metricTwoJet (cylinderBlend epsilon H z.2) 0 - cylinderModelJet =
      metricTwoJet (fun p => a p • (H p - cylinderModelField p)) 0 -
        (6 * epsilon) • metricTwoJet (fun p => (1 - a p) • cylinderModelField p) 0 := by
    rw [cylinderModelJet, ← metricTwoJet_sub_of_contDiffAt
      (cylinderBlend_contDiffAt epsilon z.2 hH) hQ, cylinderBlend_sub_model]
    change metricTwoJet
      (fun p => a p • (H p - cylinderModelField p) -
        (6 * epsilon) • ((1 - a p) • cylinderModelField p)) 0 = _
    calc
      _ = metricTwoJet (fun p => a p • (H p - cylinderModelField p)) 0 -
          metricTwoJet (fun p => (6 * epsilon) •
            ((1 - a p) • cylinderModelField p)) 0 :=
        metricTwoJet_sub_of_contDiffAt (ha.smul (hH.sub hQ))
          (hacQ.const_smul (6 * epsilon))
      _ = _ := by rw [metricTwoJet_const_smul (6 * epsilon) hacQ]
  rw [hjet]
  calc
    _ ≤ ‖metricTwoJet (fun p => a p • (H p - cylinderModelField p)) 0‖ +
        ‖(6 * epsilon) • metricTwoJet (fun p => (1 - a p) • cylinderModelField p) 0‖ :=
      norm_sub_le _ _
    _ ≤ 4 * A * (810 * epsilon) + (6 * epsilon) * (4 * A * M) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) hepsilon)]
      exact add_le_add hfirst (mul_le_mul_of_nonneg_left hsecond (by positivity))
    _ = K * epsilon := by dsimp [K]; ring
    _ ≤ max K 1 * epsilon := mul_le_mul_of_nonneg_right (le_max_left _ _) hepsilon.le

end PoincareConjecture.M36
