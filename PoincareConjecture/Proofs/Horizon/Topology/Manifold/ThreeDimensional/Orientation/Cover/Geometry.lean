import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Orientation.Cover
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Covering.LocalDiffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.LocalDiffeomorph








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace Poincare.Topology.OrientationDoubleCover

variable (M : Type u) [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]


@[instance_reducible] noncomputable def chartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) (TotalSpace M) :=
  Poincare.Manifold.LocalHomeomorphLift.chartedSpace (isCoveringMap M).isLocalHomeomorph

theorem isManifold : letI := chartedSpace M
    IsManifold (𝓡 3) ∞ (TotalSpace M) :=
  Poincare.Manifold.LocalHomeomorphLift.isManifold
    (isCoveringMap M).isLocalHomeomorph (𝓡 3) ∞

theorem isLocalDiffeomorph : letI := chartedSpace M
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (proj M) :=
  Poincare.Manifold.LocalHomeomorphLift.isLocalDiffeomorph
    (isCoveringMap M).isLocalHomeomorph (𝓡 3) ∞



theorem mfderiv_proj_eq_id : letI := chartedSpace M
    ∀ p : TotalSpace M, mfderiv (𝓡 3) (𝓡 3) (proj M) p =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) := by
  let := chartedSpace M
  let := isManifold M
  intro p
  have heq : (fun y => chartAt (EuclideanSpace ℝ (Fin 3)) (proj M p)
      (proj M ((chartAt (EuclideanSpace ℝ (Fin 3)) p).symm y))) =ᶠ[
        𝓝 (chartAt (EuclideanSpace ℝ (Fin 3)) p p)] id := by
    filter_upwards [(chartAt (EuclideanSpace ℝ (Fin 3)) p).open_target.mem_nhds
      ((chartAt (EuclideanSpace ℝ (Fin 3)) p).map_source (mem_chart_source _ p))] with y hy
    change chartAt (EuclideanSpace ℝ (Fin 3)) (proj M p)
      (proj M ((Poincare.Manifold.LocalHomeomorphLift.localChart
        (isCoveringMap M).isLocalHomeomorph p).symm y)) = y
    rw [Poincare.Manifold.LocalHomeomorphLift.projection_localChart_symm
      (isCoveringMap M).isLocalHomeomorph p hy]
    exact (chartAt (EuclideanSpace ℝ (Fin 3)) (proj M p)).right_inv hy.1
  rw [MDifferentiableAt.mfderiv (((isLocalDiffeomorph M) p).mdifferentiableAt (by simp))]
  simpa only [writtenInExtChartAt, Function.comp_def, mfld_simps, fderivWithin_univ] using
    heq.fderiv_eq.trans (fderiv_id (𝕜 := ℝ))

theorem extChartAt_eq_comp_proj : letI := chartedSpace M
    ∀ p : TotalSpace M,
      (extChartAt (𝓡 3) p : TotalSpace M → EuclideanSpace ℝ (Fin 3)) =
        extChartAt (𝓡 3) (proj M p) ∘ proj M := by
  let := chartedSpace M
  intro p
  funext q
  exact Poincare.Manifold.LocalHomeomorphLift.localChart_apply
    (isCoveringMap M).isLocalHomeomorph p q


theorem mfderiv_extChartAt_proj : letI := chartedSpace M
    ∀ (p q : TotalSpace M), q ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) p).source →
      mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) (proj M p)) (proj M q) =
        mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) p) q := by
  let := chartedSpace M
  let := isManifold M
  intro p q hq
  have hb : proj M q ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) (proj M p)).source := by
    have h := hq.2
    change (((isCoveringMap M).isLocalHomeomorph.localInverseAt p).symm q) ∈
      (chartAt (EuclideanSpace ℝ (Fin 3)) (proj M p)).source at h
    simpa only [IsLocalHomeomorph.localInverseAt_symm] using h
  have hcomp := mfderiv_comp q (mdifferentiableAt_extChartAt hb)
    (((isLocalDiffeomorph M) q).mdifferentiableAt (by simp))
  rw [← extChartAt_eq_comp_proj M p] at hcomp
  ext v
  have hv := congrArg (fun L => L v) hcomp
  rw [mfderiv_proj_eq_id] at hv
  exact hv.symm

theorem t2Space [T2Space M] : T2Space (TotalSpace M) := by
  constructor
  intro p q hne
  by_cases hpq : proj M p = proj M q
  · exact (isCoveringMap M).isSeparatedMap p q hpq hne
  · obtain ⟨U, V, hU, hV, hp, hq, hUV⟩ := t2_separation hpq
    exact ⟨proj M ⁻¹' U, proj M ⁻¹' V,
      hU.preimage (isCoveringMap M).continuous, hV.preimage (isCoveringMap M).continuous,
      hp, hq, hUV.preimage (proj M)⟩

theorem t3Space [T2Space M] : T3Space (TotalSpace M) := by
  let := chartedSpace M
  let := t2Space M
  let : LocallyCompactSpace (TotalSpace M) :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) (TotalSpace M)
  infer_instance

theorem locallyPathConnectedSpace : LocallyPathConnectedSpace (TotalSpace M) := by
  let := chartedSpace M
  exact ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) (TotalSpace M)

theorem secondCountableTopology [CompactSpace M] : SecondCountableTopology (TotalSpace M) := by
  let := chartedSpace M
  let := compactSpace M
  exact ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin 3)) (TotalSpace M)


theorem contMDiff_flip : letI := chartedSpace M
    ContMDiff (𝓡 3) (𝓡 3) ∞ (flip M) := by
  let := chartedSpace M
  apply Poincare.Manifold.LocalHomeomorphLift.contMDiff_of_continuous_projection
    (isCoveringMap M).isLocalHomeomorph (𝓡 3) ∞ (continuous_flip M)
  exact (isLocalDiffeomorph M).contMDiff


theorem mfderiv_flip_eq_id : letI := chartedSpace M
    ∀ p : TotalSpace M, mfderiv (𝓡 3) (𝓡 3) (flip M) p =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) := by
  let := chartedSpace M
  let := isManifold M
  intro p
  have hcomp := mfderiv_comp p
    (((isLocalDiffeomorph M) (flip M p)).mdifferentiableAt (by simp))
    ((contMDiff_flip M p).mdifferentiableAt (by simp))
  change mfderiv (𝓡 3) (𝓡 3) (proj M) p =
    (mfderiv (𝓡 3) (𝓡 3) (proj M) (flip M p)).comp
      (mfderiv (𝓡 3) (𝓡 3) (flip M) p) at hcomp
  ext v
  have hv := congrArg (fun L => L v) hcomp
  rw [mfderiv_proj_eq_id, mfderiv_proj_eq_id] at hv
  exact hv.symm


noncomputable def flipDiffeomorph : letI := chartedSpace M
    Diffeomorph (𝓡 3) (𝓡 3) (TotalSpace M) (TotalSpace M) ∞ := by
  let := chartedSpace M
  exact {
    toEquiv := (flipHomeomorph M).toEquiv
    contMDiff_toFun := contMDiff_flip M
    contMDiff_invFun := contMDiff_flip M
  }


theorem flip_preserves_pullback_metric (g : PoincareConjecture.RiemannianMetric 3 M) :
    letI := chartedSpace M
    letI := isManifold M
    ∀ (p : TotalSpace M) (v w : TangentSpace (𝓡 3) p),
      (g.pullbackOfLocalDiffeomorph (proj M) (isLocalDiffeomorph M)).inner (flip M p)
        (mfderiv (𝓡 3) (𝓡 3) (flip M) p v) (mfderiv (𝓡 3) (𝓡 3) (flip M) p w) =
      (g.pullbackOfLocalDiffeomorph (proj M) (isLocalDiffeomorph M)).inner p v w := by
  let := chartedSpace M
  let := isManifold M
  intro p v w
  have hderiv : (mfderiv (𝓡 3) (𝓡 3) (proj M) (flip M p)).comp
      (mfderiv (𝓡 3) (𝓡 3) (flip M) p) = mfderiv (𝓡 3) (𝓡 3) (proj M) p := by
    rw [← mfderiv_comp p (((isLocalDiffeomorph M) _).mdifferentiableAt (by simp))
      ((contMDiff_flip M p).mdifferentiableAt (by simp))]
    rfl
  simp only [PoincareConjecture.RiemannianMetric.pullbackOfLocalDiffeomorph_inner]
  change g.inner (proj M (flip M p))
    (((mfderiv (𝓡 3) (𝓡 3) (proj M) (flip M p)).comp
      (mfderiv (𝓡 3) (𝓡 3) (flip M) p)) v)
    (((mfderiv (𝓡 3) (𝓡 3) (proj M) (flip M p)).comp
      (mfderiv (𝓡 3) (𝓡 3) (flip M) p)) w) = _
  rw [hderiv, proj_flip]

end Poincare.Topology.OrientationDoubleCover
