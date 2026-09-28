import PoincareConjecture.Proofs.M65.Def18_23_Profile.RestartedProfile
import Mathlib.Analysis.Calculus.MeanValue









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Icc a b)}





theorem m65Area_le_profile_of_upperRight
    (compact : IsCompact (univ : Set M)) (A : ℝ → ℝ) {s t : ℝ}
    (hst : s ≤ t) (hsub : Icc s t ⊆ Ioo a b) (hA : ContinuousOn A (Icc s t))
    (hupper : ∀ q ∈ Ico s t, ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ h in 𝓝[>] (0 : ℝ), (A (q + h) - A q) / h ≤
        -2 * Real.pi - (flowScalarCurvatureInfimum F q / 2) * A q + epsilon) :
    ∀ q ∈ Icc s t, A q ≤ m65RestartedAreaProfile F s (A s) q := by
  let P := m65RestartedAreaProfile F s (A s)
  let alpha := fun q => flowScalarCurvatureInfimum F q / 2
  let W := fun q => Real.exp (-(∫ r in a..q, flowScalarCurvatureInfimum F r / 2))
  let beta := fun q => (q - s + 1) * W q
  have hW (q : ℝ) : 0 < W q := Real.exp_pos _
  have hderivP (q : ℝ) (hq : q ∈ Icc s t) :
      HasDerivAt P (-2 * Real.pi - alpha q * P q) q := by
    have hd := m65RestartedAreaProfile_hasDerivWithinAt F compact s (A s)
      (Ioo_subset_Icc_self (hsub hq))
    exact (hd.hasDerivAt (Icc_mem_nhds (hsub hq).1 (hsub hq).2)).congr_deriv
      (by dsimp [P, alpha]; ring)
  have hderivBeta (q : ℝ) (hq : q ∈ Icc s t) :
      HasDerivAt beta (W q - alpha q * beta q) q := by
    have hd := (areaComparisonPrimitive_hasDerivWithinAt F compact
      (Ioo_subset_Icc_self (hsub hq))).hasDerivAt
        (Icc_mem_nhds (hsub hq).1 (hsub hq).2)
    have hprod := (((hasDerivAt_id q).sub_const s).add_const 1).mul hd.neg.exp
    exact hprod.congr_deriv (by dsimp [beta, W, alpha]; ring)
  have hfreq : ∀ q ∈ Ico s t, ∀ v : ℝ,
      -2 * Real.pi - alpha q * A q < v →
      ∃ᶠ y in 𝓝[>] q, slope A q y < v := by
    intro q hq v hv
    have hepsilon : 0 < (v - (-2 * Real.pi - alpha q * A q)) / 2 := by linarith
    have hshift : Tendsto (fun y : ℝ => y - q) (𝓝[>] q) (𝓝[>] (0 : ℝ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · have hc : ContinuousAt (fun y : ℝ => y - q) q := by fun_prop
        simpa only [sub_self] using hc.tendsto.mono_left
          (nhdsWithin_le_nhds (s := Ioi q))
      · filter_upwards [self_mem_nhdsWithin] with y hy
        exact sub_pos.mpr (show q < y from hy)
    have hnear := hshift.eventually (hupper q hq _ hepsilon)
    apply Filter.Eventually.frequently
    filter_upwards [hnear] with y hy
    have heq : q + (y - q) = y := by ring
    rw [heq] at hy
    rw [slope_def_field]
    dsimp only [alpha] at hv hy ⊢
    linarith
  have hbarrier (epsilon : ℝ) (hepsilon : 0 < epsilon) :
      ∀ q ∈ Icc s t, A q ≤ P q + epsilon * beta q := by
    apply image_le_of_liminf_slope_right_lt_deriv_boundary' hA hfreq
    · have hs : s ∈ Icc s t := ⟨le_rfl, hst⟩
      have hpos : 0 < beta s := by simpa [beta] using hW s
      simp only [P, m65RestartedAreaProfile_initial]
      linarith [mul_pos hepsilon hpos]
    · have hpcont : ContinuousOn P (Icc s t) :=
        fun q hq => (hderivP q hq).continuousAt.continuousWithinAt
      have hbcont : ContinuousOn beta (Icc s t) :=
        fun q hq => (hderivBeta q hq).continuousAt.continuousWithinAt
      exact hpcont.add (continuousOn_const.mul hbcont)
    · intro q hq
      exact ((hderivP q (Ico_subset_Icc_self hq)).add
        ((hderivBeta q (Ico_subset_Icc_self hq)).const_mul epsilon)).hasDerivWithinAt
    · intro q _ hcontact
      rw [hcontact]
      nlinarith [mul_pos hepsilon (hW q)]
  intro q hq
  have hlimit : Tendsto (fun epsilon : ℝ => P q + epsilon * beta q)
      (𝓝[>] (0 : ℝ)) (𝓝 (P q)) := by
    have hc : ContinuousAt (fun epsilon : ℝ => P q + epsilon * beta q) 0 := by fun_prop
    simpa only [zero_mul, add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlimit (by
    filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
    exact hbarrier epsilon hepsilon q hq)

end PoincareConjecture
