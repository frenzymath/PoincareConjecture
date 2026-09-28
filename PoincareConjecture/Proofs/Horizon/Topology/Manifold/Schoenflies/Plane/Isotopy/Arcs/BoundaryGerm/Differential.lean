import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Germ.SphereDifferential







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.BoundaryGerm

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private instance : Fact (Module.finrank Real E2 = 1 + 1) := ⟨by simp⟩


theorem fderiv_eq_self_on_fixed_circle_patch
    {D : E2 -> E2} (hD : ContDiff Real ∞ D)
    {U : Set E2} (hU : IsOpen U)
    (hfix : ∀ x ∈ U ∩ sphere (0 : E2) 1, D x = x)
    (p : S1) (hpU : (p : E2) ∈ U)
    (u : E2) (hu : inner Real (p : E2) u = 0) : fderiv Real D p u = u := by
  let L : TangentSpace (𝓡 1) p →L[Real] E2 :=
    mfderiv (𝓡 1) (𝓡 2) (Subtype.val : S1 -> E2) p
  have hrange : L.range = (Real ∙ (p : E2))ᗮ := by
    convert! range_mvfderiv_subtypeVal p
  have heq : D ∘ (Subtype.val : S1 -> E2) =ᶠ[𝓝 p] (Subtype.val : S1 -> E2) := by
    filter_upwards [continuous_subtype_val.continuousAt.eventually (hU.mem_nhds hpU)] with q hq
    exact hfix q ⟨hq, q.property⟩
  have hchain := mfderiv_comp p (hD.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
    ((contMDiff_coe_sphere (n := 1) p).mdifferentiableAt
      (show (∞ : ℕ∞ω) ≠ 0 by simp))
  rw [heq.mfderiv_eq (I := 𝓡 1) (I' := 𝓡 2), mfderiv_eq_fderiv] at hchain
  have huL : u ∈ L.range := by
    rw [hrange, Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact hu
  obtain ⟨w, rfl⟩ := huL
  exact (congrArg (fun A => A w) hchain).symm



theorem positive_normal_of_inward_circle_patch
    {D : E2 -> E2} (hD : ContDiff Real ∞ D)
    {U : Set E2} (hU : IsOpen U)
    (hfix : ∀ x ∈ U ∩ sphere (0 : E2) 1, D x = x)
    (p : S1) (hpU : (p : E2) ∈ U)
    (hinj : Injective (fderiv Real D p))
    (hinside : ∀ᶠ t in 𝓝[<] (0 : Real), ‖D ((1 + t) • (p : E2))‖ ≤ 1) :
    0 < inner Real (p : E2) (fderiv Real D p p) := by
  have hDp : D p = p := hfix p ⟨hpU, p.property⟩
  have hcurve : HasDerivAt (fun t : Real => D ((1 + t) • (p : E2)))
      (fderiv Real D p p) 0 := by
    have hd := ((hasDerivAt_const (0 : Real) (1 : Real)).add (hasDerivAt_id 0)).smul_const (p : E2)
    have hD0 : HasFDerivAt D (fderiv Real D p) ((1 + (0 : Real)) • (p : E2)) := by
      simpa using (hD.differentiable (by simp) p).hasFDerivAt
    have hc := hD0.comp_hasDerivAt 0
      (show HasDerivAt (fun t : Real => (1 + t) • (p : E2)) (p : E2) 0 by simpa using hd)
    convert! hc using 1
  have hlim := hcurve.norm_sq.tendsto_slope_zero_left
  have hnonneg : 0 ≤ 2 * inner Real (p : E2) (fderiv Real D p p) := by
    simp only [zero_add, add_zero, one_smul, hDp, norm_eq_of_mem_sphere p, one_pow] at hlim
    apply ge_of_tendsto hlim
    filter_upwards [hinside, self_mem_nhdsWithin] with t ht htneg
    change 0 ≤ t⁻¹ * (‖D ((1 + t) • (p : E2))‖ ^ 2 - 1)
    apply mul_nonneg_of_nonpos_of_nonpos
    · exact inv_nonpos.mpr (le_of_lt htneg)
    · nlinarith [norm_nonneg (D ((1 + t) • (p : E2)))]
  have hne : inner Real (p : E2) (fderiv Real D p p) ≠ 0 := by
    intro hz
    have htan := fderiv_eq_self_on_fixed_circle_patch hD hU hfix p hpU
      (fderiv Real D p p) hz
    have heq : fderiv Real D p p = (p : E2) := hinj htan
    rw [heq] at hz
    simp at hz
  exact lt_of_le_of_ne (by linarith) hne.symm



theorem bijective_fderiv_homotopy_of_inward_circle_patch
    {D : E2 -> E2} (hD : ContDiff Real ∞ D)
    {U : Set E2} (hU : IsOpen U)
    (hfix : ∀ x ∈ U ∩ sphere (0 : E2) 1, D x = x)
    (p : S1) (hpU : (p : E2) ∈ U)
    (hinj : Injective (fderiv Real D p))
    (hinside : ∀ᶠ s in 𝓝[<] (0 : Real), ‖D ((1 + s) • (p : E2))‖ ≤ 1)
    {t : Real} (ht : t ∈ Icc 0 1) :
    Bijective (fderiv Real (fun y => (1 - t) • y + t • D y) p) := by
  have hd := ((hasFDerivAt_id (p : E2)).const_smul (1 - t)).add
    ((hD.differentiable (by simp) p).hasFDerivAt.const_smul t)
  change Bijective (fderiv Real ((1 - t) • (id : E2 -> E2) + t • D) (p : E2))
  rw [hd.fderiv]
  exact Reverse.bijective_convex_identity_of_positive_normal _ (p : E2) (by simp)
    (fderiv_eq_self_on_fixed_circle_patch hD hU hfix p hpU)
    (positive_normal_of_inward_circle_patch hD hU hfix p hpU hinj hinside) ht

end Poincare.Manifold.Schoenflies.PlaneArcs.BoundaryGerm
