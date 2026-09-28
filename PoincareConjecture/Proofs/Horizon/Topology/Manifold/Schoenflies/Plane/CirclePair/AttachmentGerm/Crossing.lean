import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.CirclePair.AttachmentGerm.Restriction
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



theorem normal_derivative_ne_zero_of_boundary_germ
    (P : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) (p : S1)
    (hp : (p : E2) ∈ P.source)
    (hboundary : ∀ᶠ x in 𝓝 (p : E2), x ∈ sphere (0 : E2) 1 → P x ∈ sphere (0 : E2) 1) :
    inner Real (P p) (fderiv Real P p p) ≠ 0 := by
  obtain ⟨f, hf, heq⟩ := exists_circle_restriction_of_boundary_germ P p hp hboundary
  change (Subtype.val ∘ f) =ᶠ[𝓝 p] (P ∘ Subtype.val) at heq
  have hfp : (f p : E2) = P p := heq.eq_of_nhds
  let L := mfderiv (𝓡 1) (𝓡 2) (Subtype.val : S1 → E2) p
  let J := mfderiv (𝓡 1) (𝓡 2) (Subtype.val : S1 → E2) (f p)
  let B := mfderiv (𝓡 1) (𝓡 1) f p
  have hP : IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ P (p : E2) :=
    ⟨P, hp, eqOn_refl _ _⟩
  have hPi : Injective (fderiv Real P p) := by
    rw [← mfderiv_eq_fderiv]
    exact (hP.mfderivToContinuousLinearEquiv (by simp)).injective
  have hBs : Surjective B := (hf.mfderivToContinuousLinearEquiv (by simp)).surjective
  have hchainf := mfderiv_comp p
    ((contMDiff_coe_sphere (n := 1) (m := ∞) (f p)).mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp))
  have hchainP := mfderiv_comp p (hP.mdifferentiableAt (by simp))
    ((contMDiff_coe_sphere (n := 1) (m := ∞) p).mdifferentiableAt (by simp))
  have hsame := heq.mfderiv_eq (I := 𝓡 1) (I' := 𝓡 2)
  rw [hchainf, hchainP, mfderiv_eq_fderiv] at hsame
  intro hz
  have hJrange : J.range = (Real ∙ (f p : E2))ᗮ := by
    convert! range_mvfderiv_subtypeVal (f p)
  have hmem : fderiv Real P p p ∈ J.range := by
    rw [hJrange, Submodule.mem_orthogonal_singleton_iff_inner_right, hfp]
    exact hz
  obtain ⟨y, hy⟩ := hmem
  obtain ⟨x, hxy⟩ := hBs y
  have hDp : fderiv Real P p (L x) = fderiv Real P p p := by
    have hh := congrArg (fun A => A x) hsame
    change J (B x) = fderiv Real P p (L x) at hh
    exact hh.symm.trans ((congrArg J hxy).trans hy)
  have hLx : L x = (p : E2) := hPi hDp
  have hLrange : L.range = (Real ∙ (p : E2))ᗮ := by
    convert! range_mvfderiv_subtypeVal p
  have hporth : (p : E2) ∈ (Real ∙ (p : E2))ᗮ := by
    rw [← hLrange]
    exact ⟨x, hLx⟩
  have hpp := Submodule.mem_orthogonal_singleton_iff_inner_right.mp hporth
  simp at hpp



theorem inward_radial_germ_of_outward_boundary_germ
    (P : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) (p : S1)
    (hp : (p : E2) ∈ P.source)
    (hboundary : ∀ᶠ x in 𝓝 (p : E2), x ∈ sphere (0 : E2) 1 → P x ∈ sphere (0 : E2) 1)
    (houtside : ∀ᶠ t in 𝓝[>] (0 : Real), 1 < ‖P ((1 + t) • (p : E2))‖) :
    ∀ᶠ t in 𝓝[<] (0 : Real), ‖P ((1 + t) • (p : E2))‖ < 1 := by
  have hPnorm : ‖P p‖ = 1 := mem_sphere_zero_iff_norm.mp
    ((Filter.Eventually.self_of_nhds hboundary) p.property)
  have hdP := (P.contMDiffOn.contMDiffAt (P.open_source.mem_nhds hp)).contDiffAt.differentiableAt
    (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hcurve : HasDerivAt (fun t : Real => P ((1 + t) • (p : E2)))
      (fderiv Real P p p) 0 := by
    have hd := ((hasDerivAt_const (0 : Real) (1 : Real)).add (hasDerivAt_id 0)).smul_const (p : E2)
    have hP0 : HasFDerivAt P (fderiv Real P p) ((1 + (0 : Real)) • (p : E2)) := by
      simpa using hdP.hasFDerivAt
    convert! hP0.comp_hasDerivAt 0
      (show HasDerivAt (fun t : Real => (1 + t) • (p : E2)) (p : E2) 0 by simpa using hd)
  have hright := hcurve.norm_sq.tendsto_slope_zero_right
  have hleft := hcurve.norm_sq.tendsto_slope_zero_left
  simp only [zero_add, add_zero, one_smul, hPnorm, one_pow] at hright hleft
  have hnonneg : 0 ≤ 2 * inner Real (P p) (fderiv Real P p p) := by
    apply ge_of_tendsto hright
    filter_upwards [houtside, self_mem_nhdsWithin] with t ht htpos
    change 0 ≤ t⁻¹ * (‖P ((1 + t) • (p : E2))‖ ^ 2 - 1)
    exact mul_nonneg (inv_nonneg.mpr htpos.le) (by nlinarith)
  have hnormal := normal_derivative_ne_zero_of_boundary_germ P p hp hboundary
  have hpos : 0 < 2 * inner Real (P p) (fderiv Real P p p) := by
    have : 0 < inner Real (P p) (fderiv Real P p p) :=
      lt_of_le_of_ne (by linarith) hnormal.symm
    positivity
  have hslopes := hleft.eventually (lt_mem_nhds hpos)
  filter_upwards [hslopes, self_mem_nhdsWithin] with t ht htneg
  change 0 < t⁻¹ * (‖P ((1 + t) • (p : E2))‖ ^ 2 - 1) at ht
  have hnormsq : ‖P ((1 + t) • (p : E2))‖ ^ 2 - 1 < 0 :=
    (mul_pos_iff.mp ht).resolve_left (fun hh => (not_lt_of_ge (inv_nonpos.mpr htneg.le)) hh.1) |>.2
  nlinarith [norm_nonneg (P ((1 + t) • (p : E2)))]

end Poincare.Manifold.Schoenflies.CircleAttachmentGerm
