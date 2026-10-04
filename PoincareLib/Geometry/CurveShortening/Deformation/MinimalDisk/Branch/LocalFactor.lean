import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.Branch.Gauge.Cutoff

/-!
# Finite order from an actual local matrix equation

The compact coefficient and its invertible matrix solution are genuinely
constructed. Analytic zero factorization then applies to the original
field with no matrix-solution or smallness premise. Source:
Eschenburg--Tribuzy, Conformal mappings of surfaces and Cauchy--Riemann
inequalities, preprint pp. 8--11; M65 derivation 32, seventh consumer,
for MT Lemma 19.2, printed pp. 438--439.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Topology ContDiff

namespace PoincareMT.M65Branch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem dbar_translate {F : ℂ → E} {z0 z : ℂ}
    (hF : DifferentiableAt ℝ F (z0 + z)) :
    dbar (fun w => F (z0 + w)) z = dbar F (z0 + z) := by
  have hd := hF.hasFDerivAt.comp z ((hasFDerivAt_id (𝕜 := ℝ) z).const_add z0)
  change HasFDerivAt (fun w => F (z0 + w)) _ z at hd
  simp only [dbar, hd.fderiv, ContinuousLinearMap.comp_id]

variable [CompleteSpace E] [Nontrivial E]

/-- An actual local C1 matrix equation gives the finite zero order and
a genuine nonzero C1 residual factor. Every matrix used in the proof is
constructed from the supplied coefficient. Source: Eschenburg--Tribuzy,
preprint pp. 8--11; derivation 32, seventh consumer. -/
theorem exists_power_factor_zero_of_local_matrix_equation
    {A : ℂ → E →L[ℂ] E} {F : ℂ → E} {s : Set ℂ}
    (hs : IsOpen s) (h0 : (0 : ℂ) ∈ s) (hA : ContDiffOn ℝ 1 A s)
    (hF : ContDiffOn ℝ 1 F s) (hFeq : ∀ z ∈ s, dbar F z = A z (F z))
    (hnot : ¬∀ᶠ z in 𝓝 0, F z = 0) :
    ∃ (n : ℕ) (G : ℂ → E), ContDiffAt ℝ 1 G 0 ∧ G 0 ≠ 0 ∧
      ∀ᶠ z in 𝓝 0, F z = z ^ n • G z := by
  obtain ⟨A0, R, B0, B1, δ, hR, hB0, hB1, hδ, hA0, hsupp, hval, hder, hsmall, heq⟩ :=
    exists_small_compact_coefficient hs h0 hA
  have hP := cauchyGauge_spec hR hB0 hB1 hδ hA0 hsupp hval hder hsmall
  obtain ⟨t, ht, htopen, h0t⟩ := _root_.mem_nhds_iff.mp heq
  have hFeq0 (z : ℂ) (hz : z ∈ s ∩ t) : dbar F z = A0 z (F z) := by
    rw [ht hz.2]
    exact hFeq z hz.1
  simpa only [sub_zero] using exists_power_factor_of_matrix_field
    (hs.inter htopen) ⟨h0, h0t⟩ hP.1 hP.2.2.2 hP.2.1
      (hF.mono inter_subset_left) hFeq0 hnot

/-- The actual local matrix equation has a finite power factor at any
point where the original field is not identically zero nearby. Source:
Eschenburg--Tribuzy, preprint pp. 8--11; derivation 32, seventh consumer. -/
theorem exists_power_factor_of_local_matrix_equation
    {A : ℂ → E →L[ℂ] E} {F : ℂ → E} {s : Set ℂ} {z0 : ℂ}
    (hs : IsOpen s) (hz0 : z0 ∈ s) (hA : ContDiffOn ℝ 1 A s)
    (hF : ContDiffOn ℝ 1 F s) (hFeq : ∀ z ∈ s, dbar F z = A z (F z))
    (hnot : ¬∀ᶠ z in 𝓝 z0, F z = 0) :
    ∃ (n : ℕ) (G : ℂ → E), ContDiffAt ℝ 1 G z0 ∧ G z0 ≠ 0 ∧
      ∀ᶠ z in 𝓝 z0, F z = (z - z0) ^ n • G z := by
  let A' := fun z => A (z0 + z)
  let F' := fun z => F (z0 + z)
  let s' := (fun z => z0 + z) ⁻¹' s
  have hshift : ContDiff ℝ 1 (fun z : ℂ => z0 + z) := contDiff_const.add contDiff_id
  have hs' : IsOpen s' := hs.preimage hshift.continuous
  have h0 : (0 : ℂ) ∈ s' := by simpa only [s', mem_preimage, add_zero] using hz0
  have hA' : ContDiffOn ℝ 1 A' s' := hA.comp hshift.contDiffOn (fun _ hz => hz)
  have hF' : ContDiffOn ℝ 1 F' s' := hF.comp hshift.contDiffOn (fun _ hz => hz)
  have hFeq' (z : ℂ) (hz : z ∈ s') : dbar F' z = A' z (F' z) := by
    rw [dbar_translate ((hF.contDiffAt (hs.mem_nhds hz)).differentiableAt one_ne_zero)]
    exact hFeq (z0 + z) hz
  have hback : Tendsto (fun z : ℂ => z - z0) (𝓝 z0) (𝓝 0) := by
    have hc : Continuous (fun z : ℂ => z - z0) := continuous_id.sub continuous_const
    simpa only [sub_self] using hc.tendsto z0
  have hcancel (z : ℂ) : z0 + (z - z0) = z := by abel
  have hnot' : ¬∀ᶠ z in 𝓝 0, F' z = 0 := by
    intro hzero
    apply hnot
    filter_upwards [hback.eventually hzero] with z hz
    simpa only [F', hcancel] using hz
  obtain ⟨n, g, hg, hg0, hfactor⟩ :=
    exists_power_factor_zero_of_local_matrix_equation hs' h0 hA' hF' hFeq' hnot'
  refine ⟨n, fun z => g (z - z0), ?_, ?_, ?_⟩
  · have hg' : ContDiffAt ℝ 1 g (z0 - z0) := by simpa only [sub_self] using hg
    have hc : ContDiff ℝ 1 (fun z : ℂ => z - z0) := contDiff_id.sub contDiff_const
    exact hg'.comp (f := fun z : ℂ => z - z0) z0 hc.contDiffAt
  · simpa only [sub_self] using hg0
  · filter_upwards [hback.eventually hfactor] with z hz
    simpa only [F', hcancel] using hz

end PoincareMT.M65Branch
