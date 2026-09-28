import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Surface.Normalization
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Surface.Cover
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Geometry

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RicciFlow.Splitting

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [T2Space M] [T3Space M] [ConnectedSpace M] [CompactSpace M]

theorem exists_unitSphere_two_covering_of_round_soliton
    {g : RiemannianMetric 2 M} (D : LeviCivitaData g) {φ : M → ℝ}
    (hφ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 φ)
    (hsol : ∀ x, ∀ u v : TangentSpace (𝓡 2) x,
      D.ricci x u v + D.hessian φ x u v = (1 / 2 : ℝ) * g.inner x u v)
    (hround : ConstantPositiveSectionalCurvature g D) :
    ∃ q : UnitSphere 2 → M,
      ContMDiff (𝓡 2) (𝓡 2) ∞ q ∧ Function.Surjective q ∧
      IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ q ∧ IsCoveringMap q ∧
      ∀ x (u v : TangentSpace (𝓡 2) x),
        g.inner (q x) (mfderiv (𝓡 2) (𝓡 2) q x u)
          (mfderiv (𝓡 2) (𝓡 2) q x v) = 2 * (roundSphereMetric 2).inner x u v := by
  let h := rescaledMetric g (1 / 2) (by norm_num)
  let Dh := rescaledMetric_connection g D (1 / 2) (by norm_num)
  have hsec (x : M) (u v : TangentSpace (𝓡 2) x)
      (huv : h.inner x u u * h.inner x v v - (h.inner x u v) ^ 2 ≠ 0) :
      h.leviCivitaData.sectionalCurvature x u v = 1 := by
    have hgram : g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 ≠ 0 := by
      intro hzero
      apply huv
      change (1 / 2 : ℝ) * g.inner x u u * ((1 / 2 : ℝ) * g.inner x v v) -
        ((1 / 2 : ℝ) * g.inner x u v) ^ 2 = 0
      nlinarith [hzero]
    have heq : h.leviCivitaData.sectionalCurvature x u v =
        Dh.sectionalCurvature x u v := by
      simp only [LeviCivitaData.sectionalCurvature,
        h.leviCivitaData.horizon_curvatureTensor_eq Dh]
      rfl
    rw [heq, rescaledMetric_sectionalCurvature,
      compactRoundSurface_sectionalCurvature_of_soliton D hφ hsol hround x u v hgram]
    norm_num
  obtain ⟨q, hq, hsurj, hlocal, hmetric⟩ := exists_unitSphere_two_covering h hsec
  refine ⟨q, hq, hsurj, hlocal,
    isLocalHomeomorph_iff_isCoveringMap.mp hlocal.isLocalHomeomorph, ?_⟩
  intro x u v
  have heq := hmetric x u v
  change (1 / 2 : ℝ) * g.inner (q x) (mfderiv (𝓡 2) (𝓡 2) q x u)
    (mfderiv (𝓡 2) (𝓡 2) q x v) = (roundSphereMetric 2).inner x u v at heq
  linarith

theorem exists_unitSphere_two_covering_of_round_soliton_family
    (h : ℝ → RiemannianMetric 2 M) (D : LeviCivitaData (h 0)) {φ : M → ℝ}
    (hφ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 φ)
    (hsol : ∀ x, ∀ u v : TangentSpace (𝓡 2) x,
      D.ricci x u v + D.hessian φ x u v = (1 / 2 : ℝ) * (h 0).inner x u v)
    (hround : ConstantPositiveSectionalCurvature (h 0) D)
    (hscale : ∀ t ≤ 0, ∀ (x : M) (u v : TangentSpace (𝓡 2) x),
      (h t).inner x u v = (1 - t) * (h 0).inner x u v) :
    ∃ q : UnitSphere 2 → M,
      ContMDiff (𝓡 2) (𝓡 2) ∞ q ∧ Function.Surjective q ∧
      IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ q ∧ IsCoveringMap q ∧
      ∀ t ≤ 0, ∀ x (u v : TangentSpace (𝓡 2) x),
        (h t).inner (q x) (mfderiv (𝓡 2) (𝓡 2) q x u)
          (mfderiv (𝓡 2) (𝓡 2) q x v) =
            (2 * (1 - t)) * (roundSphereMetric 2).inner x u v := by
  obtain ⟨q, hq, hsurj, hlocal, hcover, hmetric⟩ :=
    exists_unitSphere_two_covering_of_round_soliton D hφ hsol hround
  refine ⟨q, hq, hsurj, hlocal, hcover, ?_⟩
  intro t ht x u v
  rw [hscale t ht, hmetric]
  ring

end PoincareConjecture.RicciFlow.Splitting
