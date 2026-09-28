import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Transverse.RadialFrame
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Transverse.JacobiSystem



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

open ConnectionAlongCurve ConnectionVariation

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem exists_radial_parallel_jacobi
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {e : EuclideanSpace ℝ (Fin n) → M} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ U)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    (hgeo : ∀ v ∈ U, g.IsGeodesicOn (fun s : ℝ => e (s • v)) {s | s • v ∈ U})
    (hmetric : ∀ u v : EuclideanSpace ℝ (Fin n),
      g.inner (e 0) (mfderiv (𝓡 n) (𝓡 n) e 0 u)
        (mfderiv (𝓡 n) (𝓡 n) e 0 v) = inner ℝ u v)
    (θ : EuclideanSpace ℝ (Fin n)) {b : ℝ} (hb : 0 < b)
    (hsub : ∀ s ∈ Icc 0 b, s • θ ∈ U) :
    ∃ P : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
      P 0 = mfderiv (𝓡 n) (𝓡 n) e 0 ∧
      (∀ t ∈ Icc 0 b, (P t).IsInvertible) ∧
      (∀ t ∈ Icc 0 b, ∀ u v, g.inner (e (t • θ)) (P t u) (P t v) = inner ℝ u v) ∧
      (∀ t ∈ Icc 0 b, P t θ = mfderiv (𝓡 n) (𝓡 n) e (t • θ) θ) ∧
      let J : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
        fun t : ℝ => (P t).inverse.comp
        (t • mfderiv (𝓡 n) (𝓡 n) e (t • θ))
      let K : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
        fun t : ℝ => (P t).inverse.comp
        ((g.radialCurvatureOperator (e (t • θ)) (P t θ)).comp (P t))
      J 0 = 0 ∧ (∀ t ∈ Icc 0 b, ContDiffAt ℝ ∞ J t) ∧
        ∀ t ∈ Icc 0 b, HasDerivAt (deriv J) (-((K t).comp (J t))) t := by
  let q : ℝ → M := fun t => e (t • θ)
  let I : Set ℝ := {s | s • θ ∈ U}
  have hI : IsOpen I := hU.preimage (by fun_prop)
  have hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ q I := by
    intro t ht
    exact ((he.contMDiffAt (hU.mem_nhds ht)).comp t
      (show ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun s : ℝ => s • θ) t from
        contMDiffAt_iff_contDiffAt.mpr (by fun_prop))).contMDiffWithinAt
  have hg := g.isGeodesicOn_all_rays_of_neighborhood (hU.mem_nhds h0) hgeo
  obtain ⟨P, hP0, hPi, hP, hpair⟩ := g.exists_isometric_parallel_frame hb hI hq hsub
    (mfderiv (𝓡 n) (𝓡 n) e 0) (by
      intro u v
      change g.inner (e ((0 : ℝ) • θ)) _ _ = _
      erw [zero_smul]
      exact hmetric u v)
  have hvel (t : ℝ) (ht : t ∈ I) :
      mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1 = mfderiv (𝓡 n) (𝓡 n) e (t • θ) θ :=
    radial_velocity_eq_differential θ ((he.contMDiffAt (hU.mem_nhds ht)).mdifferentiableAt (by simp))
  have hrad (t : ℝ) (ht : t ∈ Icc 0 b) :
      P t θ = mfderiv (𝓡 n) (𝓡 n) e (t • θ) θ := by
    rw [← hvel t (hsub t ht)]
    apply g.parallel_frame_velocity hb hI (hg θ) hq hsub hPi hP θ _ ht
    rw [hvel 0 (by simpa [I] using h0)]
    erw [zero_smul]
    exact congrArg (fun A => A θ) hP0
  refine ⟨P, hP0, hPi, hpair, hrad, ?_⟩
  let F : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    fun t => t • mfderiv (𝓡 n) (𝓡 n) e (t • θ)
  have hF (t : ℝ) (ht : t ∈ I) (u : EuclideanSpace ℝ (Fin n)) :
      ContDiffAt ℝ ∞ (chartField q (q t) (fun s => F s u)) t := by
    simpa only [F, q, chartField, smul_apply, map_smul] using!
      contDiffAt_chartField_radialDifferential hU he θ u ht (mem_extChartAt_source _)
  have hjac (t : ℝ) (ht : t ∈ Icc 0 b) (u : EuclideanSpace ℝ (Fin n)) :
      manifoldCovDerivAlong g q (manifoldCovDerivAlong g q (fun s => F s u) 1) 1 t =
        -D.curvature (q t) (F t u) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) := by
    simpa only [F, q, smul_apply, map_smul] using!
      g.radialDifferential_covariant_jacobi D hU he hg θ u (hsub t ht)
  refine ⟨?_, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro u
    simp only [zero_smul, ContinuousLinearMap.comp_apply, zero_apply, map_zero]
  · intro t ht
    apply contDiffAt_operator_of_apply
    intro u
    exact contDiffAt_inverse_frame_field (hq.contMDiffAt (hI.mem_nhds (hsub t ht)))
      (hPi t ht) (fun v => (hP t ht v).1) (hF t (hsub t ht) u)
  · intro t ht
    have h := g.hasDerivAt_inverse_parallel_jacobi_operator D hb hI hq hsub hPi hP hF hjac ht
    dsimp only at h ⊢
    rw [hvel t (hsub t ht), ← hrad t ht] at h
    exact h

end PoincareConjecture.RiemannianMetric
