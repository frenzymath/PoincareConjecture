import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.CirclePair.AttachmentGerm.Normal
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.LocalExtension
import Mathlib.Analysis.Calculus.Deriv.Slope



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.CircleAttachmentGerm

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private instance : Fact (Module.finrank Real E2 = 1 + 1) := ⟨by simp⟩

private theorem fderiv_eq_self_on_local_circle_tangent
    {k : E2 → E2} (hk : ContDiff Real ∞ k) (p : S1)
    (hfix : ∀ᶠ x in 𝓝 (p : E2), x ∈ sphere (0 : E2) 1 → k x = x)
    (u : E2) (hu : inner Real (p : E2) u = 0) : fderiv Real k p u = u := by
  let L : TangentSpace (𝓡 1) p →L[Real] E2 :=
    mfderiv (𝓡 1) (𝓡 2) (Subtype.val : S1 → E2) p
  have hrange : L.range = (Real ∙ (p : E2))ᗮ := by
    convert! range_mvfderiv_subtypeVal p
  have heq : k ∘ (Subtype.val : S1 → E2) =ᶠ[𝓝 p] Subtype.val := by
    filter_upwards [continuous_subtype_val.continuousAt.eventually hfix] with q hq
    exact hq q.property
  have hchain := mfderiv_comp p (hk.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
    ((contMDiff_coe_sphere (n := 1) p).mdifferentiableAt (show (∞ : ℕ∞ω) ≠ 0 by simp))
  rw [heq.mfderiv_eq, mfderiv_eq_fderiv] at hchain
  have huL : u ∈ L.range := by
    rw [hrange, Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact hu
  obtain ⟨w, rfl⟩ := huL
  exact (congrArg (fun A => A w) hchain).symm



theorem normal_derivative_pos_of_local_inward
    {k : E2 → E2} (hk : ContDiff Real ∞ k) (p : S1)
    (hfix : ∀ᶠ x in 𝓝 (p : E2), x ∈ sphere (0 : E2) 1 → k x = x)
    (hinj : Injective (fderiv Real k p))
    (hinside : ∀ᶠ t in 𝓝[<] (0 : Real), ‖k ((1 + t) • (p : E2))‖ < 1) :
    0 < inner Real (p : E2) (fderiv Real k p p) := by
  have hkp : k p = p := (Filter.Eventually.self_of_nhds hfix) p.property
  have hcurve : HasDerivAt (fun t : Real => k ((1 + t) • (p : E2)))
      (fderiv Real k p p) 0 := by
    have hd := ((hasDerivAt_const (0 : Real) (1 : Real)).add (hasDerivAt_id 0)).smul_const (p : E2)
    have hk0 : HasFDerivAt k (fderiv Real k p) ((1 + (0 : Real)) • (p : E2)) := by
      simpa using (hk.differentiable (by simp) p).hasFDerivAt
    have hc := hk0.comp_hasDerivAt 0
      (show HasDerivAt (fun t : Real => (1 + t) • (p : E2)) (p : E2) 0 by simpa using hd)
    convert! hc using 1
  have hlim := hcurve.norm_sq.tendsto_slope_zero_left
  have hnonneg : 0 ≤ 2 * inner Real (p : E2) (fderiv Real k p p) := by
    simp only [zero_add, add_zero, one_smul, hkp, norm_eq_of_mem_sphere p, one_pow] at hlim
    apply ge_of_tendsto hlim
    filter_upwards [hinside, self_mem_nhdsWithin] with t ht htneg
    change 0 ≤ t⁻¹ * (‖k ((1 + t) • (p : E2))‖ ^ 2 - 1)
    apply mul_nonneg_of_nonpos_of_nonpos
    · exact inv_nonpos.mpr (le_of_lt htneg)
    · nlinarith [norm_nonneg (k ((1 + t) • (p : E2)))]
  have hne : inner Real (p : E2) (fderiv Real k p p) ≠ 0 := by
    intro hz
    have htan := fderiv_eq_self_on_local_circle_tangent hk p hfix
      (fderiv Real k p p) hz
    have heq : fderiv Real k p p = (p : E2) := hinj htan
    rw [heq] at hz
    simp at hz
  exact lt_of_le_of_ne (by linarith) hne.symm



theorem exists_disk_diffeomorph_of_local_inward_germ
    (k : E2 → E2) (p : S1) {U : Set E2} (hU : IsOpen U) (hpU : (p : E2) ∈ U)
    (hk : ContDiffOn Real ∞ k U)
    (hfix : ∀ᶠ x in 𝓝 (p : E2), x ∈ sphere (0 : E2) 1 → k x = x)
    (hinj : Injective (fderiv Real k p))
    (hinside : ∀ᶠ t in 𝓝[<] (0 : Real), ‖k ((1 + t) • (p : E2))‖ < 1) :
    ∃ G : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      G '' closedBall (0 : E2) 1 = closedBall (0 : E2) 1 ∧
      G '' ball (0 : E2) 1 = ball (0 : E2) 1 ∧
      (∀ q : S1, G q = q) ∧ (G : E2 → E2) =ᶠ[𝓝 (p : E2)] k := by
  obtain ⟨k', hk', _, heq⟩ := Poincare.Parabolic.Interior.exists_compact_smooth_extension
    isCompact_singleton hU (singleton_subset_iff.mpr hpU) hk
  have hnear : k' =ᶠ[𝓝 (p : E2)] k := heq p (mem_singleton _)
  have hfix' : ∀ᶠ x in 𝓝 (p : E2), x ∈ sphere (0 : E2) 1 → k' x = x := by
    filter_upwards [hnear, hfix] with x hx hfx
    exact fun hs => hx.trans (hfx hs)
  have hinj' : Injective (fderiv Real k' p) := by rw [hnear.fderiv_eq]; exact hinj
  have hinside' : ∀ᶠ t in 𝓝[<] (0 : Real), ‖k' ((1 + t) • (p : E2))‖ < 1 := by
    have hc : Tendsto (fun t : Real => (1 + t) • (p : E2)) (𝓝 (0 : Real)) (𝓝 (p : E2)) := by
      have h : ContinuousAt (fun t : Real => (1 + t) • (p : E2)) 0 := by fun_prop
      simpa using h.tendsto
    filter_upwards [(hnear.comp_tendsto hc).filter_mono nhdsWithin_le_nhds, hinside]
      with t ht hti
    change k' ((1 + t) • (p : E2)) = k ((1 + t) • (p : E2)) at ht
    rw [ht]
    exact hti
  obtain ⟨G, hGc, hGb, hGfix, hGerm⟩ := exists_disk_diffeomorph_of_circle_fixing_germ k' hk' p
    hfix' (normal_derivative_pos_of_local_inward hk' p hfix' hinj' hinside')
  exact ⟨G, hGc, hGb, hGfix, hGerm.trans hnear⟩

end Poincare.Manifold.Schoenflies.CircleAttachmentGerm
