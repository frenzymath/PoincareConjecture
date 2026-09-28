import PoincareConjecture.Proofs.M34.Standard.CanonicalPullbackCoefficients
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalExtension
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Pullback











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Filter Bundle VectorField
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M34

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) [Nonempty U]



theorem canonicalDomain_connection_of_metric_germ :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (g : RiemannianMetric n U) (D : LeviCivitaData g)
      (gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (DE : LeviCivitaData gE)
      (p : U) (x : EuclideanSpace ℝ (Fin n)), x ∈ U →
        (gE.euclideanCoefficients =ᶠ[𝓝 x]
          g.pullbackCoefficients (extChartAt (𝓡 n) p).symm) →
        ∀ u v : EuclideanSpace ℝ (Fin n),
          DE.euclideanConnection u v x =
            D.connection (fun _ : U => v) ((extChartAt (𝓡 n) p).symm x) u := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g D gE DE p x hx hmetric u v
  let r := (extChartAt (𝓡 n) p).symm
  have hr : ContMDiffAt (𝓡 n) (𝓡 n) ∞ r x := canonicalOpen_contMDiffAt_symm hU p x hx
  have hd : mfderiv (𝓡 n) (𝓡 n) r x =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) :=
    canonicalOpen_mfderiv_symm hU p x hx
  have hi : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) r y).IsInvertible := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [show mfderiv (𝓡 n) (𝓡 n) r y =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) from
        canonicalOpen_mfderiv_symm hU p y hy]
    exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
  have hg : ∀ᶠ y in 𝓝 x, ∀ a b : EuclideanSpace ℝ (Fin n),
      gE.inner y a b = g.inner (r y) (mfderiv (𝓡 n) (𝓡 n) r y a)
        (mfderiv (𝓡 n) (𝓡 n) r y b) := by
    filter_upwards [hmetric] with y hy a b
    exact congrArg (fun B => B a b) hy
  have hY := constantChart_contMDiff_const_field (𝓡 n) (canonicalOpen_chart_eq hU) v
  have hP := (hY (r x)).mpullback_vectorField_preimage hr hi.self_of_nhds (by simp)
  have ht := DE.connection_mpullback_of_metric_pullback D hr hi hg
    ((hY (r x)).mdifferentiableAt (by simp)) u
  erw [hd, ContinuousLinearMap.inverse_id] at ht
  have hc := DE.connection.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    (hP.mdifferentiableAt (by simp))
    ((constantChart_contMDiff_const_field (𝓡 n)
      (fun _ _ : EuclideanSpace ℝ (Fin n) => rfl) v x).mdifferentiableAt (by simp))
    (by simp) (show mpullback (𝓡 n) (𝓡 n) r (fun _ : U => v) =ᶠ[𝓝 x]
      (fun _ : EuclideanSpace ℝ (Fin n) => v) from by
        filter_upwards [hU.mem_nhds hx] with y hy
        simp only [mpullback_apply]
        erw [show mfderiv (𝓡 n) (𝓡 n) r y =
          ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) from
            canonicalOpen_mfderiv_symm hU p y hy, ContinuousLinearMap.inverse_id]
        rfl)
  exact (congrArg (fun A => A u) hc).symm.trans ht



theorem canonicalDomain_curvature_of_metric_germ :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (g : RiemannianMetric n U) (D : LeviCivitaData g)
      (gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (DE : LeviCivitaData gE)
      (p : U) (x : EuclideanSpace ℝ (Fin n)), x ∈ U →
        (gE.euclideanCoefficients =ᶠ[𝓝 x]
          g.pullbackCoefficients (extChartAt (𝓡 n) p).symm) →
        ∀ u v w : EuclideanSpace ℝ (Fin n),
          DE.curvature x u v w = D.curvature ((extChartAt (𝓡 n) p).symm x) u v w := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g D gE DE p x hx hmetric u v w
  let r := (extChartAt (𝓡 n) p).symm
  have hr : ContMDiffAt (𝓡 n) (𝓡 n) ∞ r x := canonicalOpen_contMDiffAt_symm hU p x hx
  have hd : mfderiv (𝓡 n) (𝓡 n) r x =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) :=
    canonicalOpen_mfderiv_symm hU p x hx
  have hi : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) r y).IsInvertible := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [show mfderiv (𝓡 n) (𝓡 n) r y =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) from
        canonicalOpen_mfderiv_symm hU p y hy]
    exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
  have hg : ∀ᶠ y in 𝓝 x, ∀ a b : EuclideanSpace ℝ (Fin n),
      gE.inner y a b = g.inner (r y) (mfderiv (𝓡 n) (𝓡 n) r y a)
        (mfderiv (𝓡 n) (𝓡 n) r y b) := by
    filter_upwards [hmetric] with y hy a b
    exact congrArg (fun B => B a b) hy
  have ht := DE.curvature_eq_pullback_euclidean D hr hi hg u v w
  erw [hd, ContinuousLinearMap.inverse_id] at ht
  exact ht



theorem canonicalDomain_exists_local_realization :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (g : RiemannianMetric n U) (D : LeviCivitaData g) (p : U)
      (x : EuclideanSpace ℝ (Fin n)), x ∈ U →
      ∃ (gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (DE : LeviCivitaData gE)
        (W : Set (EuclideanSpace ℝ (Fin n))),
        IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
        (∀ y ∈ W, gE.euclideanCoefficients y =
          g.pullbackCoefficients (extChartAt (𝓡 n) p).symm y) ∧
        (∀ y ∈ W, ∀ u v, DE.euclideanConnection u v y =
          D.connection (fun _ : U => v) ((extChartAt (𝓡 n) p).symm y) u) ∧
        (∀ y ∈ W, ∀ u v w, DE.curvature y u v w =
          D.curvature ((extChartAt (𝓡 n) p).symm y) u v w) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g D p x hx
  let B := g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
  have hB : ContDiffOn ℝ ∞ B U := by
    have hh := g.contDiffOn_chartCoefficients p
    rwa [canonicalOpen_extChart_target hU] at hh
  have hread (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ U) : B y = g.inner (⟨y, hy⟩ : U) :=
    RiemannianMetric.pullbackCoefficients_canonicalChart U hU g p ⟨y, hy⟩
  obtain ⟨gE, DE, W, hW, hxW, hWU, hcoeff⟩ := RiemannianMetric.exists_local_realization
    hU hx B hB (fun y hy u v => by rw [hread y hy]; exact g.symm _ u v)
      (fun y hy v hv => by rw [hread y hy]; exact g.pos _ v hv)
  refine ⟨gE, DE, W, hW, hxW, hWU, hcoeff, ?_, ?_⟩
  · intro y hy u v
    apply canonicalDomain_connection_of_metric_germ U hU g D gE DE p y (hWU hy)
    filter_upwards [hW.mem_nhds hy] with z hz
    exact hcoeff z hz
  · intro y hy u v w
    apply canonicalDomain_curvature_of_metric_germ U hU g D gE DE p y (hWU hy)
    filter_upwards [hW.mem_nhds hy] with z hz
    exact hcoeff z hz

end PoincareConjecture.M34
