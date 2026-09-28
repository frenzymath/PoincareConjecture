import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryTriangularSlice







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)




theorem m64TriangularSource_boundary_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : LoopPlane ≃ₜ LoopPlane) (hT : Differentiable ℝ T)
    (hi : Differentiable ℝ T.symm) (hsecond : ∀ p, T p 1 = p 1)
    (hpos : ∀ p, 0 < fderiv ℝ T p e0 0)
    (hzero : ∀ s, T (annulusPoint 0 s) = annulusPoint 0 s)
    (hperiod : ∀ s, T (annulusPoint curvePeriod s) = annulusPoint curvePeriod s)
    (phi : LoopPlane → ℝ) (c : ℝ → E) (s : ℝ) :
    (∫ x in Icc (0 : ℝ) curvePeriod, m64TriangularCofactorTest1 T phi
      (annulusPoint x s) • c x) =
    ∫ x in Icc (0 : ℝ) curvePeriod,
      phi (annulusPoint x s) • c (T (annulusPoint x s) 0) := by
  let tau := m64TriangularSourceSlice T hsecond s
  have ht : Differentiable ℝ tau := fun x =>
    (m64Source_horizontalSlice_hasDerivAt hT x s).differentiableAt
  have hm : StrictMono tau := strictMono_of_hasDerivAt_pos
    (fun x => m64Source_horizontalSlice_hasDerivAt hT x s)
    (fun x => hpos (annulusPoint x s))
  have h0 : tau 0 = 0 := by change T (annulusPoint 0 s) 0 = 0; rw [hzero]; rfl
  have hP : tau curvePeriod = curvePeriod := by
    change T (annulusPoint curvePeriod s) 0 = curvePeriod
    rw [hperiod]
    rfl
  rw [← m64HorizontalSource_interval_integral ht hm h0 hP
    (fun x => m64TriangularCofactorTest1 T phi (annulusPoint x s) • c x)]
  apply integral_congr_ae
  filter_upwards [] with x
  have hpoint : annulusPoint (tau x) s = T (annulusPoint x s) :=
    (m64TriangularSource_point hsecond x s).symm
  rw [m64TriangularSourceSlice_deriv T hsecond hT, hpoint, ← mul_smul,
    (m64TriangularCofactorTest_at_source T hT hi hsecond phi (annulusPoint x s)).2]
  rfl




theorem m64TriangularSource_preserves_seam
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : LoopPlane ≃ₜ LoopPlane) (hT : ContDiff ℝ ∞ T) (hi : ContDiff ℝ ∞ T.symm)
    (hsecond : ∀ p, T p 1 = p 1) (hpos : ∀ p, 0 < fderiv ℝ T p e0 0)
    (hpre : T ⁻¹' S = S)
    (hzero : ∀ s, T (annulusPoint 0 s) = annulusPoint 0 s)
    (hperiod : ∀ s, T (annulusPoint curvePeriod s) = annulusPoint curvePeriod s)
    (u V : LoopPlane → E) (d : E)
    (hseam : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s ∈ Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
      (∫ p in S, phi p • V p) + (∫ p in S, fderiv ℝ phi p e0 • u p) =
        (∫ s in Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s)) • d)
    (phi : LoopPlane → ℝ) (hp : ContDiff ℝ 1 phi)
    (hs : ∀ s ∈ Icc (0 : ℝ) 1,
      phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) :
    (∫ p in S, phi p • (fderiv ℝ T p e0 0 • V (T p))) +
      (∫ p in S, fderiv ℝ phi p e0 • u (T p)) =
      (∫ s in Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s)) • d := by
  have hz (s : ℝ) : T.symm (annulusPoint 0 s) = annulusPoint 0 s :=
    (congrArg T.symm (hzero s)).symm.trans (T.symm_apply_apply _)
  have hP (s : ℝ) : T.symm (annulusPoint curvePeriod s) = annulusPoint curvePeriod s :=
    (congrArg T.symm (hperiod s)).symm.trans (T.symm_apply_apply _)
  rw [m64TriangularSource_horizontal_green T hT hi hsecond hpos hpre u V hp]
  rw [hseam _ (hp.comp (hi.of_le (by simp))) (by
    intro s hss
    simpa only [Function.comp_apply, hz, hP] using hs s hss)]
  simp only [Function.comp_apply, hP]




theorem m64TriangularSource_preserves_boundary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : LoopPlane ≃ₜ LoopPlane) (hT : ContDiff ℝ ∞ T) (hi : ContDiff ℝ ∞ T.symm)
    (hsecond : ∀ p, T p 1 = p 1) (hpos : ∀ p, 0 < fderiv ℝ T p e0 0)
    (hpre : T ⁻¹' S = S)
    (hzero : ∀ s, T (annulusPoint 0 s) = annulusPoint 0 s)
    (hperiod : ∀ s, T (annulusPoint curvePeriod s) = annulusPoint curvePeriod s)
    {u V0 V1 : LoopPlane → E} (hu : MemLp u 2 mu)
    (hV0 : MemLp V0 2 mu) (hV1 : MemLp V1 2 mu)
    {c0 c1 : ℝ → E} (hc0 : Continuous c0) (hc1 : Continuous c1) (d : E)
    (hboundary : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∫ p in S, phi p • V1 p) + (∫ p in S, fderiv ℝ phi p e1 • u p) =
        ∫ x in Icc (0 : ℝ) curvePeriod,
          phi (annulusPoint x 1) • c1 x - phi (annulusPoint x 0) • c0 x)
    (hseam : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s ∈ Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
      (∫ p in S, phi p • V0 p) + (∫ p in S, fderiv ℝ phi p e0 • u p) =
        (∫ s in Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s)) • d)
    (phi : LoopPlane → ℝ) (hp : ContDiff ℝ 1 phi) :
    (∫ p in S, phi p • (fderiv ℝ T p e1 0 • V0 (T p) + V1 (T p))) +
      (∫ p in S, fderiv ℝ phi p e1 • u (T p)) =
      ∫ x in Icc (0 : ℝ) curvePeriod,
        phi (annulusPoint x 1) • c1 (T (annulusPoint x 1) 0) -
          phi (annulusPoint x 0) • c0 (T (annulusPoint x 0) 0) := by
  let psi0 := m64TriangularCofactorTest0 T phi
  let psi1 := m64TriangularCofactorTest1 T phi
  have hsmooth := m64TriangularCofactorTest_contDiff T hi hp (by simp)
  have ht := hT.differentiable (by simp)
  have hit := hi.differentiable (by simp)
  have hz (s : ℝ) : psi0 (annulusPoint 0 s) = 0 :=
    m64TriangularCofactorTest0_fixed_seam T hit hzero phi s
  have hP (s : ℝ) : psi0 (annulusPoint curvePeriod s) = 0 :=
    m64TriangularCofactorTest0_fixed_seam T hit hperiod phi s
  have hseam0 := hseam psi0 hsmooth.1 (by intro s _; rw [hz, hP])
  simp only [hP, integral_zero, zero_smul] at hseam0
  rw [m64TriangularSource_radial_green T hT hi hsecond hpos hpre hu hV0 hV1 hp,
    hseam0, zero_add, hboundary psi1 hsmooth.2]
  have old_integrable {c : ℝ → E} (hc : Continuous c) (s : ℝ) :
      IntegrableOn (fun x => psi1 (annulusPoint x s) • c x) (Icc 0 curvePeriod) volume := by
    have hh := (hsmooth.2.continuous.comp
      (m64Source_annulusPoint_contDiff s).continuous).smul hc
    exact hh.continuousOn.integrableOn_compact isCompact_Icc
  have new_integrable {c : ℝ → E} (hc : Continuous c) (s : ℝ) :
      IntegrableOn (fun x => phi (annulusPoint x s) • c (T (annulusPoint x s) 0))
        (Icc 0 curvePeriod) volume := by
    have hh := (hp.continuous.comp (m64Source_annulusPoint_contDiff s).continuous).smul
      (hc.comp (m64TriangularSourceSlice T hsecond s).continuous)
    exact hh.continuousOn.integrableOn_compact isCompact_Icc
  rw [integral_sub (old_integrable hc1 1) (old_integrable hc0 0),
    m64TriangularSource_boundary_integral T ht hit hsecond hpos hzero hperiod,
    m64TriangularSource_boundary_integral T ht hit hsecond hpos hzero hperiod,
    integral_sub (new_integrable hc1 1) (new_integrable hc0 0)]

end PoincareConjecture
