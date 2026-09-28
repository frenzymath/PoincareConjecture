import PoincareConjecture.Proofs.M14.Mathlib.ConvexLinearApproximation
import PoincareConjecture.Proofs.M14.Mathlib.InitialFamilyNeighborhood
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Normed.Module.FiniteDimension











set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology NNReal

namespace PoincareConjecture.M14

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]




theorem exists_open_initial_operator_injective
    {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U)
    {b : ℝ} (hb : 0 < b) (D : ℝ × E → E →L[ℝ] H)
    (hD : ContDiffOn ℝ ∞ D (Icc 0 b ×ˢ U))
    (hzero : ∀ y ∈ U, D (0, y) = 0) (L : E →L[ℝ] H)
    (hL : Function.Injective L)
    (hjet : fderivWithin ℝ D (Icc 0 b ×ˢ U) (0, x) (1, 0) = L) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ d : ℝ, 0 < d ∧ d ≤ b ∧
        ∀ y ∈ V, ∀ s ∈ Ioc 0 d, Function.Injective (D (s, y)) := by
  obtain ⟨ρ, hρ, hρU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let B := Metric.ball x ρ
  have hB : IsOpen B := Metric.isOpen_ball
  have hxB : x ∈ B := Metric.mem_ball_self hρ
  let S := Icc (0 : ℝ) b ×ˢ B
  have hsub : S ⊆ Icc 0 b ×ˢ U := prod_mono Subset.rfl hρU
  have hS : UniqueDiffOn ℝ S := (uniqueDiffOn_Icc hb).prod hB.uniqueDiffOn
  have hcenter : ((0 : ℝ), x) ∈ S := ⟨⟨le_rfl, hb.le⟩, hxB⟩
  have hDS := hD.mono hsub
  let A := fderivWithin ℝ D S (0, x)
  have hA : A (1, 0) = L := by
    rw [show A = fderivWithin ℝ D (Icc 0 b ×ˢ U) (0, x) from
      fderivWithin_subset hsub (hS (0, x) hcenter)
        ((hD (0, x) (hsub hcenter)).differentiableWithinAt (by simp))]
    exact hjet
  obtain ⟨ε, hε, hεinj⟩ := Metric.mem_nhds_iff.mp
    (ContinuousLinearMap.isOpen_injective.mem_nhds hL)
  let c : ℝ≥0 := ⟨ε / 2, (half_pos hε).le⟩
  have hc : 0 < c := half_pos hε
  obtain ⟨O, hO, hxO, happ⟩ := exists_open_approximatesLinearOn
    ((convex_Icc (0 : ℝ) b).prod (convex_ball x ρ)) hS
    (hDS.of_le (by simp)) hcenter c hc
  have hnear : {z : E × ℝ | (z.2, z.1) ∈ O} ∈ 𝓝[B ×ˢ Icc 0 b] (x, 0) :=
    mem_nhdsWithin_of_mem_nhds
      ((hO.preimage (continuous_snd.prodMk continuous_fst)).mem_nhds hxO)
  obtain ⟨V, hV, hxV, hVB, d, hd, hdb, hVO⟩ :=
    exists_open_initial_family_neighborhood hB hxB hb hnear
  refine ⟨V, hV, hxV, hVB.trans hρU, d, hd, hdb, ?_⟩
  intro y hy s hs
  have hsC : s ∈ Icc 0 b := ⟨hs.1.le, hs.2.trans hdb⟩
  have hsD : s ∈ Icc 0 d := Ioc_subset_Icc_self hs
  have h0D : (0 : ℝ) ∈ Icc 0 d := ⟨le_rfl, hd.le⟩
  have hySO : (s, y) ∈ O := hVO (show (y, s) ∈ V ×ˢ Icc 0 d from ⟨hy, hsD⟩)
  have hy0O : ((0 : ℝ), y) ∈ O :=
    hVO (show (y, (0 : ℝ)) ∈ V ×ˢ Icc 0 d from ⟨hy, h0D⟩)
  have hbnd := happ (s, y) ⟨hySO, hsC, hVB hy⟩
    (0, y) ⟨hy0O, ⟨le_rfl, hb.le⟩, hVB hy⟩
  have hpair : (s, (0 : E)) = s • ((1 : ℝ), (0 : E)) := by simp
  change ‖D (s, y) - D (0, y) - A ((s, y) - (0, y))‖ ≤
    (c : ℝ) * ‖(s, y) - (0, y)‖ at hbnd
  simp only [Prod.mk_sub_mk, sub_zero, sub_self, hzero y (hρU (hVB hy))] at hbnd
  rw [hpair, map_smul, hA] at hbnd
  have hnorm : ‖(s, (0 : E))‖ = s := by
    rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg s), Real.norm_of_nonneg hs.1.le]
  have hnorm' : ‖s • ((1 : ℝ), (0 : E))‖ = s := hpair ▸ hnorm
  rw [hnorm'] at hbnd
  have hscaled : s⁻¹ • D (s, y) - L = s⁻¹ • (D (s, y) - s • L) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hs.1.ne', one_smul]
  have hbound : ‖s⁻¹ • D (s, y) - L‖ ≤ (c : ℝ) := by
    rw [hscaled, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs.1)]
    calc
      s⁻¹ * ‖D (s, y) - s • L‖ ≤ s⁻¹ * ((c : ℝ) * s) :=
        mul_le_mul_of_nonneg_left hbnd (inv_nonneg.mpr hs.1.le)
      _ = c := by field_simp [hs.1.ne']
  have hinj : Function.Injective (s⁻¹ • D (s, y)) := hεinj (by
    rw [Metric.mem_ball, dist_eq_norm]
    exact hbound.trans_lt (half_lt_self hε))
  intro v w hvw
  apply hinj
  change s⁻¹ • D (s, y) v = s⁻¹ • D (s, y) w
  rw [hvw]

end PoincareConjecture.M14
