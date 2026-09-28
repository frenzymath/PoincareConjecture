import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.ParallelJacobi
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Transverse.RadialFrame









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.SpaceForm

open ConnectionAlongCurve ConnectionVariation

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



theorem normalJacobi_inner_self
    (D : LeviCivitaData g) {q : ℝ → M} {I : Set ℝ} {b : ℝ}
    (hb : 0 < b) (hI : IsOpen I)
    (hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ q I) (hsub : Icc 0 b ⊆ I)
    (hgeo : g.IsGeodesicOn q I)
    (hunit : g.inner (q 0)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q 0 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q 0 1) = 1)
    (J : (t : ℝ) → TangentSpace (𝓡 n) (q t))
    (hJ : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField q (q t) J) t)
    (hjac : ∀ t ∈ Icc 0 b,
      manifoldCovDerivAlong g q (manifoldCovDerivAlong g q J 1) 1 t =
        -D.curvature (q t) (J t)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1))
    (hsec : ∀ t ∈ Icc 0 b, ∀ u v : TangentSpace (𝓡 n) (q t),
      g.inner (q t) u u * g.inner (q t) v v - (g.inner (q t) u v) ^ 2 ≠ 0 →
        D.sectionalCurvature (q t) u v = 1)
    (hJ0 : J 0 = 0)
    (hnormal : g.inner (q 0) (manifoldCovDerivAlong g q J 1 0)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q 0 1) = 0) {t : ℝ} (ht : t ∈ Icc 0 b) :
    g.inner (q t) (J t) (J t) = Real.sin t ^ 2 *
      g.inner (q 0) (manifoldCovDerivAlong g q J 1 0)
        (manifoldCovDerivAlong g q J 1 0) := by
  obtain ⟨P, _, _, hpair, hformula, _⟩ := exists_parallel_spherical_jacobi D
    hb hI hq hsub (fun s => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q s 1) J
    (fun s hs => RiemannianMetric.contDiffAt_chartField_velocity hI hq hs
      (mem_extChartAt_source _))
    (fun s hs => hgeo.manifoldCovDeriv_velocity_eq_zero hI hq (hsub hs))
    hunit hJ hjac hsec hJ0 hnormal
  rw [hformula t ht]
  simp only [map_smul, smul_apply, smul_eq_mul, hpair t ht]
  ring

end PoincareConjecture.SpaceForm
