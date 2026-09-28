import PoincareConjecture.Proofs.M35.Thm12_28.NeckMetricJets










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem exists_translated_metric
    (g : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))) (D : LeviCivitaData g)
    (p : EuclideanSpace ℝ (Fin 3)) :
    ∃ (G : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))) (DG : LeviCivitaData G),
      (∀ y v w : EuclideanSpace ℝ (Fin 3), G.inner y v w = g.inner (y + p) v w) ∧
      DG.curvatureTensorNorm 0 = D.curvatureTensorNorm p := by
  let E := EuclideanSpace ℝ (Fin 3)
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let f : E → E := fun y => y + p
  have hf : ContDiff ℝ ∞ f := contDiff_id.add contDiff_const
  have hB : ContDiff ℝ ∞ (fun y => g.euclideanCoefficients (f y)) :=
    (contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients).comp hf
  let G := RiemannianMetric.ofEuclideanCoefficients
    (fun y => g.euclideanCoefficients (f y)) hB
    (fun y v w => g.symm (f y) v w) (fun y v hv => g.pos (f y) v hv)
  let DG := G.euclideanLeviCivitaData
  have hd (y : E) : mfderiv (𝓡 3) (𝓡 3) f y = ContinuousLinearMap.id ℝ E := by
    rw [mfderiv_eq_fderiv]
    exact ((hasFDerivAt_id y).add_const p).fderiv
  have hinv : ∀ᶠ y in 𝓝 (0 : E), (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible := by
    apply Filter.Eventually.of_forall
    intro y
    rw [hd]
    exact ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩
  have hmetric : ∀ᶠ y in 𝓝 (0 : E), ∀ v w : E,
      G.inner y v w = g.inner (f y) (mfderiv (𝓡 3) (𝓡 3) f y v)
        (mfderiv (𝓡 3) (𝓡 3) f y w) := by
    apply Filter.Eventually.of_forall
    intro y v w
    rw [hd]
    rfl
  refine ⟨G, DG, fun _ _ _ => rfl, ?_⟩
  have h := LeviCivitaData.curvatureTensorNorm_eq_pullback_euclidean
    (n := 3) (gE := G) (h := g) (f := f) (x := 0) DG D
    hf.contMDiff.contMDiffAt hinv hmetric
  simpa only [f, zero_add] using h

end PoincareConjecture.M35

namespace PoincareConjecture.StandardCylinderPatch




theorem exists_axial_curvature_realization {length : ℝ} {center : StandardCapSpace}
    (N : StandardCylinderPatch length center)
    (g : RiemannianMetric 3 StandardCapSpace) (D : LeviCivitaData g)
    (q : UnitTwoSphere) (s : ℝ) (hs : s ∈ Ioo (-length) length) :
    ∃ (G : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))) (DG : LeviCivitaData G),
      (∀ i j : Fin 3,
        (fun y : EuclideanSpace ℝ (Fin 3) => G.inner y
          (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)) =ᶠ[𝓝 0]
        (fun y => roundCylinderTensorCoefficient (roundCylinderPullback g N.coordinate)
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) (M35.cylinderCoordinateEquiv y + (0, s)) i j)) ∧
      DG.curvatureTensorNorm 0 = D.curvatureTensorNorm (N.coordinate (q, s)) := by
  let p := M35.cylinderCoordinateEquiv.symm (0, s)
  have hp : M35.cylinderCoordinateEquiv p = (0, s) :=
    M35.cylinderCoordinateEquiv.apply_symm_apply (0, s)
  have hdom : (M35.cylinderCoordinateEquiv p).2 ∈ Ioo (-length) length := by
    simpa only [hp] using hs
  obtain ⟨G, DG, hG, hnorm⟩ := N.exists_euclidean_curvature_realization g D q hdom
  obtain ⟨H, DH, hH, hnormH⟩ := M35.exists_translated_metric G DG p
  have hshift : Tendsto (fun y : EuclideanSpace ℝ (Fin 3) => y + p) (𝓝 0) (𝓝 p) := by
    have h : ContinuousAt (fun y : EuclideanSpace ℝ (Fin 3) => y + p) 0 :=
      continuousAt_id.add continuousAt_const
    simpa only [ContinuousAt, zero_add] using h
  refine ⟨H, DH, ?_, ?_⟩
  · intro i j
    have hc := N.euclidean_realization_coefficient_germ g q hdom G hG i j
    filter_upwards [hc.comp_tendsto hshift] with y hy
    rw [hH]
    exact hy.trans (by simp only [Function.comp_apply, map_add, hp])
  · have hc : M35.cylinderChart q p = (q, s) := by
      change ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm
        (M35.cylinderCoordinateEquiv p).1, (M35.cylinderCoordinateEquiv p).2) = _
      rw [hp]
      apply Prod.ext
      · have h := (chartAt (EuclideanSpace ℝ (Fin 2)) q).left_inv
          (mem_chart_source (EuclideanSpace ℝ (Fin 2)) q)
        simpa only [M35.sphere_chart_center] using h
      · rfl
    exact hnormH.trans (hnorm.trans
      (congrArg D.curvatureTensorNorm (congrArg N.coordinate hc)))

end PoincareConjecture.StandardCylinderPatch
