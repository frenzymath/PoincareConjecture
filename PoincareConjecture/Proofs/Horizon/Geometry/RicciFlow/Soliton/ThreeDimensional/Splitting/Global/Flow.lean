import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Completeness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Pullback
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometryInvariants











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RicciFlow.Splitting

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} (F : RicciFlow n M J)
  (hc : IsCoveringMap (unitRicciKernelProjection (F.connection 0)))


def unitRicciKernelFlow :
    letI := unitRicciKernelChartedSpace (F.connection 0) hc
    letI := unitRicciKernelIsManifold (F.connection 0) hc
    RicciFlow n (UnitRicciKernel (F.connection 0)) J := by
  let := unitRicciKernelChartedSpace (F.connection 0) hc
  let := unitRicciKernelIsManifold (F.connection 0) hc
  exact F.pullbackWithConnection (unitRicciKernelProjection (F.connection 0))
    (unitRicciKernelProjection_isLocalDiffeomorph (F.connection 0) hc)
    (fun t => ((F.metric t).pullbackOfLocalDiffeomorph
      (unitRicciKernelProjection (F.connection 0))
      (unitRicciKernelProjection_isLocalDiffeomorph (F.connection 0) hc)).leviCivitaData)

@[simp] theorem unitRicciKernelFlow_inner (t : ℝ)
    (p : UnitRicciKernel (F.connection 0)) :
    letI := unitRicciKernelChartedSpace (F.connection 0) hc
    letI := unitRicciKernelIsManifold (F.connection 0) hc
    ∀ v w : TangentSpace (𝓡 n) p,
      ((unitRicciKernelFlow F hc).metric t).inner p v w =
        (F.metric t).inner (unitRicciKernelProjection (F.connection 0) p)
          (mfderiv (𝓡 n) (𝓡 n) (unitRicciKernelProjection (F.connection 0)) p v)
          (mfderiv (𝓡 n) (𝓡 n) (unitRicciKernelProjection (F.connection 0)) p w) := by
  let := unitRicciKernelChartedSpace (F.connection 0) hc
  let := unitRicciKernelIsManifold (F.connection 0) hc
  intro v w
  rfl

@[simp] theorem unitRicciKernelFlow_metric_zero :
    letI := unitRicciKernelChartedSpace (F.connection 0) hc
    letI := unitRicciKernelIsManifold (F.connection 0) hc
    (unitRicciKernelFlow F hc).metric 0 = unitRicciKernelMetric (F.connection 0) hc := rfl

@[simp] theorem unitRicciKernelFlow_connection_zero :
    letI := unitRicciKernelChartedSpace (F.connection 0) hc
    letI := unitRicciKernelIsManifold (F.connection 0) hc
    (unitRicciKernelFlow F hc).connection 0 =
      (unitRicciKernelMetric (F.connection 0) hc).leviCivitaData := rfl


theorem unitRicciKernelFlow_metricComplete [T3Space M]
    (hcard : ∀ x, Nat.card (unitRicciKernelProjection (F.connection 0) ⁻¹' {x}) = 2)
    (t : ℝ) (hcomplete : MetricComplete (F.metric t)) :
    letI := unitRicciKernelChartedSpace (F.connection 0) hc
    letI := unitRicciKernelIsManifold (F.connection 0) hc
    letI := unitRicciKernelT3Space (F.connection 0) hc
    MetricComplete ((unitRicciKernelFlow F hc).metric t) := by
  let := unitRicciKernelChartedSpace (F.connection 0) hc
  let := unitRicciKernelIsManifold (F.connection 0) hc
  let := unitRicciKernelT3Space (F.connection 0) hc
  exact metricComplete_of_proper_metric_pullback ((unitRicciKernelFlow F hc).metric t)
    (F.metric t) (unitRicciKernelProjection_isLocalDiffeomorph (F.connection 0) hc).contMDiff
    (unitRicciKernelProjection_isProperMap (F.connection 0) hc hcard)
    (fun _ _ _ => rfl) hcomplete

theorem unitRicciKernelFlow_ricci (t : ℝ)
    (p : UnitRicciKernel (F.connection 0)) :
    letI := unitRicciKernelChartedSpace (F.connection 0) hc
    letI := unitRicciKernelIsManifold (F.connection 0) hc
    ∀ v w : TangentSpace (𝓡 n) p,
      ((unitRicciKernelFlow F hc).connection t).ricci p v w =
        (F.connection t).ricci (unitRicciKernelProjection (F.connection 0) p)
          (mfderiv (𝓡 n) (𝓡 n) (unitRicciKernelProjection (F.connection 0)) p v)
          (mfderiv (𝓡 n) (𝓡 n) (unitRicciKernelProjection (F.connection 0)) p w) := by
  let := unitRicciKernelChartedSpace (F.connection 0) hc
  let := unitRicciKernelIsManifold (F.connection 0) hc
  intro v w
  exact ((unitRicciKernelFlow F hc).connection t).ricci_eq_of_local_isometry
    (F.connection t) isOpen_univ
    (unitRicciKernelProjection_isLocalDiffeomorph (F.connection 0) hc).contMDiff.contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ p) v w


@[simp] theorem unitRicciKernelFlow_ricciNullity (t : ℝ)
    (p : UnitRicciKernel (F.connection 0)) :
    letI := unitRicciKernelChartedSpace (F.connection 0) hc
    letI := unitRicciKernelIsManifold (F.connection 0) hc
    ricciNullity ((unitRicciKernelFlow F hc).connection t) p =
      ricciNullity (F.connection t) (unitRicciKernelProjection (F.connection 0) p) := by
  let := unitRicciKernelChartedSpace (F.connection 0) hc
  let := unitRicciKernelIsManifold (F.connection 0) hc
  let proj := unitRicciKernelProjection (F.connection 0)
  let L := ((unitRicciKernelProjection_isLocalDiffeomorph (F.connection 0) hc).mfderivToContinuousLinearEquiv
    (by simp) p).toLinearEquiv
  have hker : ricciKernel (F.connection t) (proj p) =
      (ricciKernel ((unitRicciKernelFlow F hc).connection t) p).map L.toLinearMap := by
    ext v
    rw [Submodule.mem_map_equiv, mem_ricciKernel, mem_ricciKernel]
    constructor
    · intro hv w
      rw [unitRicciKernelFlow_ricci]
      change (F.connection t).ricci (proj p) (L (L.symm v)) (L w) = 0
      rw [L.apply_symm_apply]
      exact hv _
    · intro hv w
      obtain ⟨z, rfl⟩ := L.surjective w
      have hz := hv z
      rw [unitRicciKernelFlow_ricci] at hz
      change (F.connection t).ricci (proj p) (L (L.symm v)) (L z) = 0 at hz
      simpa only [L.apply_symm_apply] using hz
  unfold ricciNullity
  rw [hker, LinearEquiv.finrank_map_eq]

@[simp] theorem unitRicciKernelFlow_scalarCurvature (t : ℝ)
    (p : UnitRicciKernel (F.connection 0)) :
    letI := unitRicciKernelChartedSpace (F.connection 0) hc
    letI := unitRicciKernelIsManifold (F.connection 0) hc
    ((unitRicciKernelFlow F hc).connection t).scalarCurvature p =
      (F.connection t).scalarCurvature (unitRicciKernelProjection (F.connection 0) p) := by
  let := unitRicciKernelChartedSpace (F.connection 0) hc
  let := unitRicciKernelIsManifold (F.connection 0) hc
  exact ((unitRicciKernelFlow F hc).connection t).scalarCurvature_eq_of_local_isometry
    (F.connection t) isOpen_univ
    (unitRicciKernelProjection_isLocalDiffeomorph (F.connection 0) hc).contMDiff.contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ p)

@[simp] theorem unitRicciKernelFlow_curvatureTensorNorm (t : ℝ)
    (p : UnitRicciKernel (F.connection 0)) :
    letI := unitRicciKernelChartedSpace (F.connection 0) hc
    letI := unitRicciKernelIsManifold (F.connection 0) hc
    ((unitRicciKernelFlow F hc).connection t).curvatureTensorNorm p =
      (F.connection t).curvatureTensorNorm (unitRicciKernelProjection (F.connection 0) p) := by
  let := unitRicciKernelChartedSpace (F.connection 0) hc
  let := unitRicciKernelIsManifold (F.connection 0) hc
  exact ((unitRicciKernelFlow F hc).connection t).curvatureTensorNorm_eq_of_local_isometry
    (F.connection t) isOpen_univ
    (unitRicciKernelProjection_isLocalDiffeomorph (F.connection 0) hc).contMDiff.contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ p)


theorem unitRicciKernelFlow_nonnegativeCurvatureOperator_iff (t : ℝ)
    (p : UnitRicciKernel (F.connection 0)) :
    letI := unitRicciKernelChartedSpace (F.connection 0) hc
    letI := unitRicciKernelIsManifold (F.connection 0) hc
    ((unitRicciKernelFlow F hc).connection t).NonnegativeCurvatureOperator p ↔
      (F.connection t).NonnegativeCurvatureOperator
        (unitRicciKernelProjection (F.connection 0) p) := by
  let := unitRicciKernelChartedSpace (F.connection 0) hc
  let := unitRicciKernelIsManifold (F.connection 0) hc
  exact ((unitRicciKernelFlow F hc).connection t).nonnegativeCurvatureOperator_iff_of_local_isometry
    (F.connection t) isOpen_univ
    (unitRicciKernelProjection_isLocalDiffeomorph (F.connection 0) hc).contMDiff.contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ p)


theorem unitRicciKernelFlow_curvatureTensorNorm_bound
    (hbound : ∀ t ∈ J, ∃ C : ℝ, ∀ x, (F.connection t).curvatureTensorNorm x ≤ C) :
    letI := unitRicciKernelChartedSpace (F.connection 0) hc
    letI := unitRicciKernelIsManifold (F.connection 0) hc
    ∀ t ∈ J, ∃ C : ℝ, ∀ p,
      ((unitRicciKernelFlow F hc).connection t).curvatureTensorNorm p ≤ C := by
  let := unitRicciKernelChartedSpace (F.connection 0) hc
  let := unitRicciKernelIsManifold (F.connection 0) hc
  intro t ht
  obtain ⟨C, hC⟩ := hbound t ht
  refine ⟨C, fun p => ?_⟩
  rw [unitRicciKernelFlow_curvatureTensorNorm]
  exact hC _


theorem unitRicciKernelFlow_reverse_preserves_metric (t : ℝ) :
    letI := unitRicciKernelChartedSpace (F.connection 0) hc
    letI := unitRicciKernelIsManifold (F.connection 0) hc
    ∀ (p : UnitRicciKernel (F.connection 0)) (v w : TangentSpace (𝓡 n) p),
      ((unitRicciKernelFlow F hc).metric t).inner (unitRicciKernelReverse (F.connection 0) p)
        (mfderiv (𝓡 n) (𝓡 n) (unitRicciKernelReverse (F.connection 0)) p v)
        (mfderiv (𝓡 n) (𝓡 n) (unitRicciKernelReverse (F.connection 0)) p w) =
      ((unitRicciKernelFlow F hc).metric t).inner p v w := by
  let := unitRicciKernelChartedSpace (F.connection 0) hc
  let := unitRicciKernelIsManifold (F.connection 0) hc
  intro p v w
  let proj := unitRicciKernelProjection (F.connection 0)
  let r := unitRicciKernelReverse (F.connection 0)
  have hp := (unitRicciKernelProjection_isLocalDiffeomorph (F.connection 0) hc).mdifferentiable
    (by simp)
  have hr := (unitRicciKernelReverse_contMDiff (F.connection 0) hc).mdifferentiable (by simp)
  have hd : (mfderiv (𝓡 n) (𝓡 n) proj (r p)).comp (mfderiv (𝓡 n) (𝓡 n) r p) =
      mfderiv (𝓡 n) (𝓡 n) proj p := (mfderiv_comp p (hp _) (hr p)).symm
  change (F.metric t).inner (proj p)
      (mfderiv (𝓡 n) (𝓡 n) proj (r p) (mfderiv (𝓡 n) (𝓡 n) r p v))
      (mfderiv (𝓡 n) (𝓡 n) proj (r p) (mfderiv (𝓡 n) (𝓡 n) r p w)) = _
  rw [← ContinuousLinearMap.comp_apply, hd, ← ContinuousLinearMap.comp_apply, hd]
  rfl

end PoincareConjecture.RicciFlow.Splitting
