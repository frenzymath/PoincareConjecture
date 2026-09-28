import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.BoundedCylinder
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Hemisphere.Caps










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1



def northernDiskSphere {v : E3} (hv : ‖v‖ = 1)
    (x : Hemisphere.Plane v) : S2 :=
  ⟨-(stereoInvFun hv ((-2 : Real) • x) : E3), by
    rw [mem_sphere_zero_iff_norm, norm_neg, norm_eq_of_mem_sphere]⟩

private theorem northernDiskSphere_formula {v : E3} (hv : ‖v‖ = 1)
    (x : Hemisphere.Plane v) :
    (northernDiskSphere hv x : E3) =
      (1 + ‖x‖ ^ 2)⁻¹ • ((2 : Real) • (x : E3) + (1 - ‖x‖ ^ 2) • v) := by
  change -((‖((-2 : Real) • x : Hemisphere.Plane v)‖ ^ 2 + 4)⁻¹ •
    ((4 : Real) • (((-2 : Real) • x : Hemisphere.Plane v) : E3) +
      (‖((-2 : Real) • x : Hemisphere.Plane v)‖ ^ 2 - 4) • v)) = _
  norm_num only [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by norm_num : (0 : Real) < 2),
    Submodule.coe_smul]
  have h : 1 + ‖x‖ ^ 2 ≠ 0 := by positivity
  have h4 : (2 * ‖x‖) ^ 2 + 4 ≠ 0 := by positivity
  rw [show ((2 * ‖x‖) ^ 2 + 4)⁻¹ = (1 / 4 : Real) * (1 + ‖x‖ ^ 2)⁻¹ by
    field_simp; ring]
  module

private theorem northernDiskSphere_height {v : E3} (hv : ‖v‖ = 1)
    (x : Hemisphere.Plane v) :
    inner Real v (northernDiskSphere hv x : E3) =
      (1 - ‖x‖ ^ 2) / (1 + ‖x‖ ^ 2) := by
  have hx := Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property
  simp [northernDiskSphere_formula, inner_smul_right, inner_add_right, hx, hv,
    div_eq_mul_inv, mul_comm]


theorem image_closedBall_northernDiskSphere {v : E3} (hv : ‖v‖ = 1) :
    northernDiskSphere hv '' closedBall (0 : Hemisphere.Plane v) 1 =
      {p : S2 | 0 ≤ inner Real v (p : E3)} := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_ofPred_eq, northernDiskSphere_height]
    apply div_nonneg _ (by positivity)
    have hnx := mem_closedBall_zero_iff.mp hx
    nlinarith [norm_nonneg x]
  · intro hp
    let p' : S2 := ⟨-(p : E3), by simp⟩
    have hp' : p' ∈ {p : S2 | inner Real v (p : E3) ≤ 0} := by
      change inner Real v (-(p : E3)) ≤ 0
      simpa using hp
    rw [← Hemisphere.image_closedBall_stereoInvFun hv
      (by norm_num : (-1 : Real) < 0) (by norm_num : (0 : Real) < 1)] at hp'
    obtain ⟨y, hy, hyp⟩ := hp'
    have hy2 : ‖y‖ ≤ 2 := by
      norm_num [mem_closedBall_zero_iff, Hemisphere.complementRadius] at hy
      have hsqrt : Real.sqrt 4 = 2 := by
        rw [show (4 : Real) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      simpa only [hsqrt, Submodule.coe_norm] using hy
    refine ⟨(- (1 / 2) : Real) • y, ?_, ?_⟩
    · rw [mem_closedBall_zero_iff, norm_smul]
      norm_num only [Real.norm_eq_abs, abs_neg, abs_of_pos (by norm_num : (0 : Real) < 1 / 2)]
      linarith
    · apply Subtype.ext
      change -(stereoInvFun hv ((-2 : Real) • ((-(1 / 2) : Real) • y)) : E3) = _
      rw [smul_smul, show (-2 : Real) * (-(1 / 2)) = 1 by norm_num, one_smul, hyp]
      exact neg_neg (p : E3)

private theorem contDiff_northernDiskSphere {v : E3} (hv : ‖v‖ = 1) :
    ContDiff Real ∞ (fun x : Hemisphere.Plane v => (northernDiskSphere hv x : E3)) := by
  have hs : ContDiff Real ∞ (fun x : Hemisphere.Plane v => ((-2 : Real) • x : E3)) :=
    (Hemisphere.Plane v).subtypeL.contDiff.const_smul (-2 : Real)
  exact ((contDiff_stereoInvFunAux (v := v)).comp hs).neg

private theorem northernDiskSphere_injective {v : E3} (hv : ‖v‖ = 1) :
    Function.Injective (fun x : Hemisphere.Plane v => (northernDiskSphere hv x : E3)) := by
  intro x y h
  have h' := congrArg (stereoToFun v) (neg_injective h)
  simp only [stereo_right_inv] at h'
  exact smul_right_injective (Hemisphere.Plane v) (by norm_num : (-2 : Real) ≠ 0) h'

private theorem northernDiskSphere_fderiv_injective {v : E3} (hv : ‖v‖ = 1)
    (x : Hemisphere.Plane v) :
    Function.Injective (fderiv Real
      (fun y : Hemisphere.Plane v => (northernDiskSphere hv y : E3)) x) := by
  let p : Hemisphere.Plane v → E3 := fun y => northernDiskSphere hv y
  let k : E3 → Hemisphere.Plane v := fun y => (-2 : Real)⁻¹ • stereoToFun v (-y)
  have hkp : k ∘ p = id := by
    funext y
    change (-2 : Real)⁻¹ • stereoToFun v
      (-(-(stereoInvFun hv ((-2 : Real) • y) : E3))) = y
    rw [neg_neg, stereo_right_inv, inv_smul_smul₀ (by norm_num : (-2 : Real) ≠ 0)]
  have hreg : innerSL Real v (-p x) ≠ 1 := by
    change inner Real v (-(-(stereoInvFun hv ((-2 : Real) • x) : E3))) ≠ 1
    rw [neg_neg]
    rw [Hemisphere.inner_stereoInvFun]
    intro h
    have hd : 0 < ‖((-2 : Real) • x : Hemisphere.Plane v)‖ ^ 2 + 4 := by positivity
    have := (div_eq_iff (ne_of_gt hd)).mp h
    linarith
  have hk : DifferentiableAt Real k (p x) := by
    have hst : ContDiffAt Real ∞ (stereoToFun v) (-p x) :=
      contDiffOn_stereoToFun.contDiffAt
        ((isOpen_ne.preimage (innerSL Real v).continuous).mem_nhds hreg)
    exact ((hst.comp _ contDiffAt_id.neg).const_smul ((-2 : Real)⁻¹)).differentiableAt
      (by simp)
  have hp := (contDiff_northernDiskSphere hv).differentiable (by simp) x
  have hd := fderiv_comp x hk hp
  rw [hkp, fderiv_id] at hd
  intro a b hab
  have h := congrArg (fderiv Real k (p x)) hab
  have ha := congrArg (fun L : Hemisphere.Plane v →L[Real] Hemisphere.Plane v => L a) hd
  have hb := congrArg (fun L : Hemisphere.Plane v →L[Real] Hemisphere.Plane v => L b) hd
  exact ha.trans (h.trans hb.symm)

private theorem northernDiskSphere_bounded_collar {v : E3} (hv : ‖v‖ = 1)
    (q : Hemisphere.Plane v) (hq : ‖q‖ = 1)
    {ρ : Real} (hρ : 3 / 4 ≤ ρ) (hρ1 : ρ ≤ 4 / 3) :
    boundedCylinderRadius v (northernDiskSphere hv (ρ • q)) •
        (northernDiskSphere hv (ρ • q) : E3) =
      (q : E3) + ((1 - ρ ^ 2) / (2 * ρ)) • v := by
  have hρ0 : 0 < ρ := by linarith
  have hn : ‖ρ • q‖ = ρ := by
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos hρ0, hq]
  have hd : 0 < 1 + ρ ^ 2 := by positivity
  have hh0 : -(1 / 2) ≤ (1 - ρ ^ 2) / (1 + ρ ^ 2) := by
    rw [le_div_iff₀ hd]
    nlinarith [mul_nonneg (sub_nonneg.mpr hρ1)
      (show 0 ≤ 4 / 3 + ρ by linarith)]
  have hh1 : (1 - ρ ^ 2) / (1 + ρ ^ 2) ≤ 1 / 2 := by
    rw [div_le_iff₀ hd]
    nlinarith [sq_nonneg (ρ - 3 / 4)]
  have hh : |inner Real v (northernDiskSphere hv (ρ • q) : E3)| ≤ 1 / 2 := by
    rw [northernDiskSphere_height, hn]
    exact abs_le.mpr ⟨hh0, hh1⟩
  have hs : 1 - ((1 - ρ ^ 2) / (1 + ρ ^ 2)) ^ 2 =
      (2 * ρ / (1 + ρ ^ 2)) ^ 2 := by
    field_simp
    ring
  have hsqrt : Real.sqrt (1 - ((1 - ρ ^ 2) / (1 + ρ ^ 2)) ^ 2) =
      2 * ρ / (1 + ρ ^ 2) := by
    rw [hs, Real.sqrt_sq (by positivity)]
  rw [boundedCylinderRadius_of_abs_height_le v _ hh, northernDiskSphere_height,
    northernDiskSphere_formula, hn, hsqrt, Submodule.coe_smul]
  have ha : (2 * ρ / (1 + ρ ^ 2))⁻¹ * (1 + ρ ^ 2)⁻¹ = (2 * ρ)⁻¹ := by
    field_simp
  rw [smul_smul, ha, smul_add, smul_smul, smul_smul]
  have hqcoef : (2 * ρ)⁻¹ * 2 * ρ = 1 := by field_simp
  rw [smul_smul, hqcoef, one_smul]
  congr 1
  congr 1
  rw [div_eq_mul_inv, mul_comm]





theorem exists_northern_cylindrical_cap_with_range (v : E3) (hv : ‖v‖ = 1) :
    ∃ g : Hemisphere.Plane v → E3,
      ContDiff Real ∞ g ∧ Function.Injective g ∧
      (∀ x, Function.Injective (fderiv Real g x)) ∧
      (∀ x, ‖x‖ = 1 → g x = (x : E3)) ∧
      (∀ x, ‖x‖ < 1 → 0 < inner Real v (g x)) ∧
      (∀ q : Hemisphere.Plane v, ‖q‖ = 1 → ∀ ρ : Real,
        3 / 4 ≤ ρ → ρ ≤ 4 / 3 →
        g (ρ • q) = (q : E3) + ((1 - ρ ^ 2) / (2 * ρ)) • v) ∧
      (∀ x, ‖(Hemisphere.Plane v).orthogonalProjectionOnto (g x)‖ ≤ 1 ∧
        |inner Real v (g x)| ≤ 2) ∧
      g '' closedBall (0 : Hemisphere.Plane v) 1 =
        (fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
          {p : S2 | 0 ≤ inner Real v (p : E3)} := by
  obtain ⟨F, _, hF, hFproj, hFheight⟩ := exists_boundedCylinder_ambient v hv
  let p : Hemisphere.Plane v → E3 := fun x => northernDiskSphere hv x
  let g : Hemisphere.Plane v → E3 := F ∘ p
  have hgd : ContDiff Real ∞ g :=
    F.contMDiff.contDiff.comp (contDiff_northernDiskSphere hv)
  have hgc (q : Hemisphere.Plane v) (hq : ‖q‖ = 1)
      (ρ : Real) (hρ : 3 / 4 ≤ ρ) (hρ1 : ρ ≤ 4 / 3) :
      g (ρ • q) = (q : E3) + ((1 - ρ ^ 2) / (2 * ρ)) • v := by
    change F (northernDiskSphere hv (ρ • q)) = _
    rw [hF]
    exact northernDiskSphere_bounded_collar hv q hq hρ hρ1
  refine ⟨g, hgd, F.injective.comp (northernDiskSphere_injective hv), ?_, ?_, ?_, hgc,
    (fun x => ⟨hFproj (northernDiskSphere hv x), hFheight (northernDiskSphere hv x)⟩), ?_⟩
  · intro x
    have hFd : Function.Injective (fderiv Real F (p x)) := by
      have h := (F.mfderivToContinuousLinearEquiv (by simp) (p x)).injective
      change Function.Injective (mfderiv (𝓡 3) (𝓡 3) F (p x)) at h
      simpa only [mfderiv_eq_fderiv, TangentSpace] using h
    rw [show g = F ∘ p from rfl, fderiv_comp x
      (F.contMDiff.contDiff.differentiable (by simp) (p x))
      ((contDiff_northernDiskSphere hv).differentiable (by simp) x)]
    exact hFd.comp (northernDiskSphere_fderiv_injective hv x)
  · intro x hx
    simpa using hgc x hx 1 (by norm_num) (by norm_num)
  · intro x hx
    change 0 < inner Real v (F (northernDiskSphere hv x))
    rw [hF, inner_smul_right, northernDiskSphere_height]
    apply mul_pos (boundedCylinderRadius_pos v _)
    apply div_pos _ (by positivity)
    nlinarith [norm_nonneg x]
  · have heq : g = (fun p : S2 => boundedCylinderRadius v p • (p : E3)) ∘
        northernDiskSphere hv := funext fun x => hF (northernDiskSphere hv x)
    rw [heq, Set.image_comp, image_closedBall_northernDiskSphere]


theorem exists_northern_cylindrical_cap (v : E3) (hv : ‖v‖ = 1) :
    ∃ g : Hemisphere.Plane v → E3,
      ContDiff Real ∞ g ∧ Function.Injective g ∧
      (∀ x, Function.Injective (fderiv Real g x)) ∧
      (∀ x, ‖x‖ = 1 → g x = (x : E3)) ∧
      (∀ x, ‖x‖ < 1 → 0 < inner Real v (g x)) ∧
      (∀ q : Hemisphere.Plane v, ‖q‖ = 1 → ∀ ρ : Real,
        3 / 4 ≤ ρ → ρ ≤ 4 / 3 →
        g (ρ • q) = (q : E3) + ((1 - ρ ^ 2) / (2 * ρ)) • v) ∧
      (∀ x, ‖(Hemisphere.Plane v).orthogonalProjectionOnto (g x)‖ ≤ 1 ∧
        |inner Real v (g x)| ≤ 2) := by
  obtain ⟨g, hg, hi, hd, hb, hh, hc, hbound, _⟩ :=
    exists_northern_cylindrical_cap_with_range v hv
  exact ⟨g, hg, hi, hd, hb, hh, hc, hbound⟩



theorem exists_southern_cylindrical_cap (v : E3) (hv : ‖v‖ = 1) :
    ∃ g : Hemisphere.Plane v → E3,
      ContDiff Real ∞ g ∧ Function.Injective g ∧
      (∀ x, Function.Injective (fderiv Real g x)) ∧
      (∀ x, ‖x‖ = 1 → g x = (x : E3)) ∧
      (∀ x, ‖x‖ < 1 → inner Real v (g x) < 0) ∧
      (∀ q : Hemisphere.Plane v, ‖q‖ = 1 → ∀ ρ : Real,
        3 / 4 ≤ ρ → ρ ≤ 4 / 3 →
        g (ρ • q) = (q : E3) - ((1 - ρ ^ 2) / (2 * ρ)) • v) ∧
      (∀ x, ‖(Hemisphere.Plane v).orthogonalProjectionOnto (g x)‖ ≤ 1 ∧
        |inner Real v (g x)| ≤ 2) := by
  obtain ⟨g, hgd, hgi, hgder, hgb, hgh, hgc, hgbound⟩ := exists_northern_cylindrical_cap v hv
  let s : Hemisphere.Plane v → E3 := fun x => -g (-x)
  refine ⟨s, (hgd.comp contDiff_id.neg).neg,
    neg_injective.comp (hgi.comp neg_injective), ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    have hder := ((hgd.differentiable (by simp) (-x)).hasFDerivAt.comp x
      (hasFDerivAt_id x).neg).neg
    have heq : fderiv Real s x =
        -(fderiv Real g (-x) ∘L (-ContinuousLinearMap.id Real (Hemisphere.Plane v))) :=
      hder.fderiv
    rw [heq]
    intro a b hab
    apply neg_injective
    apply hgder (-x)
    exact neg_injective hab
  · intro x hx
    change -g (-x) = _
    rw [hgb (-x) (by simpa using hx)]
    simp
  · intro x hx
    have hh := hgh (-x) (by simpa using hx)
    simpa only [s, inner_neg_right, neg_lt_zero] using hh
  · intro q hq ρ hρ hρ1
    change -g (-(ρ • q)) = _
    rw [← smul_neg, hgc (-q) (by simpa using hq) ρ hρ hρ1]
    simp [sub_eq_add_neg, add_comm]
  · intro x
    simpa only [s, map_neg, norm_neg, inner_neg_right, abs_neg] using hgbound (-x)

end Poincare.Manifold.Schoenflies
