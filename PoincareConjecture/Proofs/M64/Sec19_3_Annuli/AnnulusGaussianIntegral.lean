import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusConnectionForm

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Annulus_gaussian_integral_eq_connection_boundary
    (g : RiemannianMetric 2 LoopPlane) (D : LeviCivitaData g)
    (e0 e1 : LoopPlane → LoopPlane) {O : Set LoopPlane}
    (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (he0 : ContDiffOn ℝ ∞ e0 O) (he1 : ContDiffOn ℝ ∞ e1 O)
    (hunit0 : ∀ p ∈ O, g.inner p (e0 p) (e0 p) = 1)
    (hunit1 : ∀ p ∈ O, g.inner p (e1 p) (e1 p) = 1)
    (horth : ∀ p ∈ O, g.inner p (e0 p) (e1 p) = 0)
    (hpositive : ∀ p ∈ O, 0 ≤
      g.inner p (EuclideanSpace.single (0 : Fin 2) 1) (e0 p) *
          g.inner p (EuclideanSpace.single (1 : Fin 2) 1) (e1 p) -
        g.inner p (EuclideanSpace.single (0 : Fin 2) 1) (e1 p) *
          g.inner p (EuclideanSpace.single (1 : Fin 2) 1) (e0 p))
    (hseam : ∀ s ∈ Icc (0 : ℝ) 1,
      g.inner (annulusPoint curvePeriod s)
          (D.connection e0 (annulusPoint curvePeriod s) (EuclideanSpace.single (1 : Fin 2) 1))
          (e1 (annulusPoint curvePeriod s)) =
        g.inner (annulusPoint 0 s)
          (D.connection e0 (annulusPoint 0 s) (EuclideanSpace.single (1 : Fin 2) 1))
          (e1 (annulusPoint 0 s))) :
    (∫ p in m64AnnulusDomain,
      (D.scalarCurvature p / 2) * g.pullbackVolumeDensity (fun q : LoopPlane => q) p) =
      ∫ x in Icc (0 : ℝ) curvePeriod,
        g.inner (annulusPoint x 1)
            (D.connection e0 (annulusPoint x 1) (EuclideanSpace.single (0 : Fin 2) 1))
            (e1 (annulusPoint x 1)) -
          g.inner (annulusPoint x 0)
            (D.connection e0 (annulusPoint x 0) (EuclideanSpace.single (0 : Fin 2) 1))
            (e1 (annulusPoint x 0)) := by
  let b0 : LoopPlane := EuclideanSpace.single (0 : Fin 2) 1
  let b1 : LoopPlane := EuclideanSpace.single (1 : Fin 2) 1
  have hpoint (p : LoopPlane) (hp : p ∈ O) :
      (D.scalarCurvature p / 2) * g.pullbackVolumeDensity (fun q : LoopPlane => q) p =
        -D.curvatureTensor p b0 b1 (e1 p) (e0 p) := by
    have hden := LeviCivitaData.pullbackVolumeDensity_eq_abs_frameDet
      (f := fun q : LoopPlane => q) (x := p) g (e0 p) (e1 p)
        (hunit0 p hp) (hunit1 p hp) (horth p hp)
    have hid : mfderiv (𝓡 2) (𝓡 2) (fun q : LoopPlane => q) p =
        ContinuousLinearMap.id ℝ LoopPlane := mfderiv_id
    have hden' : g.pullbackVolumeDensity (fun q : LoopPlane => q) p =
        g.inner p b0 (e0 p) * g.inner p b1 (e1 p) -
          g.inner p b0 (e1 p) * g.inner p b1 (e0 p) := by
      rw [hid] at hden
      simp only [EuclideanSpace.basisFun_apply] at hden
      change g.pullbackVolumeDensity (fun q : LoopPlane => q) p =
        |g.inner p b0 (e0 p) * g.inner p b1 (e1 p) -
          g.inner p b0 (e1 p) * g.inner p b1 (e0 p)| at hden
      rwa [abs_of_nonneg (hpositive p hp)] at hden
    rw [hden', D.curvatureTensor_eq_half_scalarCurvature]
    ring
  have heq : (∫ p in m64AnnulusDomain,
      (D.scalarCurvature p / 2) * g.pullbackVolumeDensity (fun q : LoopPlane => q) p) =
        -(∫ p in m64AnnulusDomain, D.curvatureTensor p b0 b1 (e1 p) (e0 p)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem m64AnnulusDomain_measurableSet] with p hp
    exact hpoint p (hdom hp)
  have hboundary := m64Annulus_connectionForm_curvature_integral
    g D e0 e1 hO hdom he0 he1 hunit0 hunit1 horth hseam
  rw [heq]
  linarith

end PoincareConjecture
