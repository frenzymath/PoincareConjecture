import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_NormalJacobiEquation
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Transverse.RadialFrame

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

open ConnectionAlongCurve ConnectionVariation

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_boundary_unit_tangent_inner
    (N : IntrinsicAnnulus) {radius : ℝ} (hradius : radius ≠ 0) (a : ℝ) :
    N.metric.inner (intrinsicAnnulusBoundary radius a)
      (intrinsicBoundaryUnitTangent N.metric radius a)
      (intrinsicBoundaryUnitTangent N.metric radius a) = 1 := by
  have hs := m64Intrinsic_boundarySpeed_pos N hradius a
  have hsq : intrinsicBoundarySpeed N.metric radius a ^ 2 =
      N.metric.inner (intrinsicAnnulusBoundary radius a)
        (curveVelocity (n := 2) (intrinsicAnnulusBoundary radius) a)
        (curveVelocity (n := 2) (intrinsicAnnulusBoundary radius) a) :=
    Real.sq_sqrt (Real.sqrt_pos.mp hs).le
  simp only [intrinsicBoundaryUnitTangent, map_smul, smul_apply, smul_eq_mul, ← hsq]
  field_simp

theorem m64Intrinsic_exists_normal_parallel_frame
    (N : IntrinsicAnnulus) {radius : ℝ} (hradius : radius ≠ 0) (a : ℝ)
    {normal : AnnulusCoordinates}
    (hunit : N.metric.inner (intrinsicAnnulusBoundary radius a) normal normal = 1)
    (horth : N.metric.inner (intrinsicAnnulusBoundary radius a) normal
      (curveVelocity (n := 2) (intrinsicAnnulusBoundary radius) a) = 0)
    {q : ℝ → AnnulusCoordinates} {I : Set ℝ} {b : ℝ} (hb : 0 < b)
    (hI : IsOpen I) (hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 2) ∞ q I)
    (hsub : Icc (0 : ℝ) b ⊆ I) (hgeo : N.metric.IsGeodesicOn q I)
    (hqzero : q 0 = intrinsicAnnulusBoundary radius a)
    (hqvelocity : HasDerivAt q normal 0) :
    ∃ P : ℝ → AnnulusCoordinates →L[ℝ] AnnulusCoordinates,
      P 0 !₂[1, 0] = normal ∧
      P 0 !₂[0, 1] = intrinsicBoundaryUnitTangent N.metric radius a ∧
      (∀ t ∈ Icc (0 : ℝ) b, (P t).IsInvertible) ∧
      (∀ t ∈ Icc (0 : ℝ) b, ∀ u,
        ContDiffAt ℝ ∞ (chartField q (q t) (fun s => P s u)) t ∧
        manifoldCovDerivAlong N.metric q (fun s => P s u) 1 t = 0) ∧
      (∀ t ∈ Icc (0 : ℝ) b, ∀ u v,
        N.metric.inner (q t) (P t u) (P t v) = inner ℝ u v) ∧
      ∀ t ∈ Icc (0 : ℝ) b, P t !₂[1, 0] = curveVelocity (n := 2) q t := by
  let T : AnnulusCoordinates := intrinsicBoundaryUnitTangent N.metric radius a
  let L : AnnulusCoordinates →L[ℝ] AnnulusCoordinates :=
    (EuclideanSpace.proj 0).smulRight normal + (EuclideanSpace.proj 1).smulRight T
  have hTunit := m64Intrinsic_boundary_unit_tangent_inner N hradius a
  change N.metric.inner (intrinsicAnnulusBoundary radius a) T T = 1 at hTunit
  have hNT : N.metric.inner (intrinsicAnnulusBoundary radius a) normal T = 0 := by
    change N.metric.inner (intrinsicAnnulusBoundary radius a) normal
      ((intrinsicBoundarySpeed N.metric radius a)⁻¹ •
        curveVelocity (n := 2) (intrinsicAnnulusBoundary radius) a) = 0
    rw [map_smul, smul_eq_mul, horth, mul_zero]
  have hTN : N.metric.inner (intrinsicAnnulusBoundary radius a) T normal = 0 := by
    rw [N.metric.symm]
    exact hNT
  have hL (u v : AnnulusCoordinates) :
      N.metric.inner (q 0) (L u) (L v) = inner ℝ u v := by
    rw [hqzero]
    change N.metric.inner (intrinsicAnnulusBoundary radius a)
      (u 0 • normal + u 1 • T) (v 0 • normal + v 1 • T) = inner ℝ u v
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul,
      hunit, hTunit, hNT, hTN, mul_zero, mul_one, zero_add, add_zero,
      PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply]
    ring
  have hL0 : L !₂[1, 0] = normal := by
    change (1 : ℝ) • normal + (0 : ℝ) • T = normal
    simp
  have hL1 : L !₂[0, 1] = T := by
    change (0 : ℝ) • normal + (1 : ℝ) • T = T
    simp
  obtain ⟨P, hP0, hPi, hP, hpair⟩ :=
    N.metric.exists_isometric_parallel_frame hb hI hq hsub L hL
  refine ⟨P, hP0 ▸ hL0, hP0 ▸ hL1, hPi, hP, hpair, ?_⟩
  intro t ht
  apply N.metric.parallel_frame_velocity hb hI hgeo hq hsub hPi hP !₂[1, 0] _ ht
  change P 0 !₂[1, 0] = curveVelocity (n := 2) q 0
  rw [hP0, hL0, m64Intrinsic_curveVelocity_eq_deriv, hqvelocity.deriv]

end PoincareConjecture
