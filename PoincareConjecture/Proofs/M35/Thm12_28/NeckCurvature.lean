import PoincareConjecture.Proofs.M35.Thm12_28.NeckCharts
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Pullback

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.StandardCylinderPatch

variable {length : ℝ} {center : StandardCapSpace}

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem exists_euclidean_metric_realization (N : StandardCylinderPatch length center)
    (g : RiemannianMetric 3 StandardCapSpace)
    (q : UnitTwoSphere) {p : EuclideanSpace ℝ (Fin 3)}
    (hp : (M35.cylinderCoordinateEquiv p).2 ∈ Ioo (-length) length) :
    ∃ (g' : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)))
      (_D' : LeviCivitaData g'),
      ∀ᶠ y in 𝓝 p, g'.euclideanCoefficients y =
        g.pullbackCoefficients (N.coordinate ∘ M35.cylinderChart q) y := by
  let : NormedAddCommGroup (EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) := inferInstance
  let : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) := inferInstance
  let U : Set (EuclideanSpace ℝ (Fin 3)) :=
    {y | (M35.cylinderCoordinateEquiv y).2 ∈ Ioo (-length) length}
  let f := N.coordinate ∘ M35.cylinderChart q
  have hU : IsOpen U := isOpen_Ioo.preimage
    (continuous_snd.comp M35.cylinderCoordinateEquiv.continuous)
  have hf (y : EuclideanSpace ℝ (Fin 3)) (hy : y ∈ U) :
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ f y := N.euclideanChart_contMDiffAt q hy
  have hi (y : EuclideanSpace ℝ (Fin 3)) (hy : y ∈ U) :
      (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible := N.euclideanChart_mfderiv_invertible q hy
  obtain ⟨g', D', V, hV, hpV, _, hcoeff⟩ :=
    RiemannianMetric.exists_local_realization hU hp (g.pullbackCoefficients f)
      (fun y hy => (g.contDiffAt_pullbackCoefficients (hf y hy)).contDiffWithinAt)
      (fun y _ v w => g.symm (f y) _ _)
      (fun y hy v hv => by
        apply g.pos (f y)
        intro hz
        apply hv
        apply (hi y hy).injective
        exact hz.trans (map_zero (mfderiv (𝓡 3) (𝓡 3) f y)).symm)
  exact ⟨g', D', Filter.mem_of_superset (hV.mem_nhds hpV) hcoeff⟩

theorem exists_euclidean_curvature_realization (N : StandardCylinderPatch length center)
    (g : RiemannianMetric 3 StandardCapSpace) (D : LeviCivitaData g)
    (q : UnitTwoSphere) {p : EuclideanSpace ℝ (Fin 3)}
    (hp : (M35.cylinderCoordinateEquiv p).2 ∈ Ioo (-length) length) :
    ∃ (g' : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)))
      (D' : LeviCivitaData g'),
      (∀ᶠ y in 𝓝 p, g'.euclideanCoefficients y =
        g.pullbackCoefficients (N.coordinate ∘ M35.cylinderChart q) y) ∧
      D'.curvatureTensorNorm p = D.curvatureTensorNorm (N.coordinate (M35.cylinderChart q p)) := by
  let : NormedAddCommGroup (EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) := inferInstance
  let : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) := inferInstance
  obtain ⟨g', D', heq⟩ := N.exists_euclidean_metric_realization g q hp
  let U : Set (EuclideanSpace ℝ (Fin 3)) :=
    {y | (M35.cylinderCoordinateEquiv y).2 ∈ Ioo (-length) length}
  let f := N.coordinate ∘ M35.cylinderChart q
  have hU : IsOpen U := isOpen_Ioo.preimage
    (continuous_snd.comp M35.cylinderCoordinateEquiv.continuous)
  have hinv : ∀ᶠ y in 𝓝 p, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible :=
    Filter.mem_of_superset (hU.mem_nhds hp) (fun _ hy => N.euclideanChart_mfderiv_invertible q hy)
  have hmetric : ∀ᶠ y in 𝓝 p, ∀ v w : EuclideanSpace ℝ (Fin 3),
      g'.inner y v w = g.inner (f y) (mfderiv (𝓡 3) (𝓡 3) f y v)
        (mfderiv (𝓡 3) (𝓡 3) f y w) := by
    filter_upwards [heq] with y hy v w
    exact congrArg (fun B : EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ => B v w) hy
  refine ⟨g', D', heq, ?_⟩
  exact LeviCivitaData.curvatureTensorNorm_eq_pullback_euclidean
    (n := 3) (gE := g') (h := g) (f := f) (x := p) D' D
    (N.euclideanChart_contMDiffAt q hp) hinv hmetric

end PoincareConjecture.StandardCylinderPatch
