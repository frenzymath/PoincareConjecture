import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Soliton
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Flow
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.ComponentCover
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Surface.Scalar

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RicciFlow

open Splitting RiemannianMetric

theorem scalarCurvature_eq_one_of_terminal_null_plane
    {M : Type u} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow 3 M (Iic 0))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (hnonflat : ∃ p, (F.connection 0).curvatureTensorNorm p ≠ 0)
    (hcomplete : MetricComplete (F.metric 0))
    (f : M → ℝ) (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ y, ∀ v w, (F.connection 0).ricci y v w +
      (F.connection 0).hessian f y v w = (1 / 2 : ℝ) * (F.metric 0).inner y v w)
    (x : M) (v w : TangentSpace (𝓡 3) x)
    (hv : (F.metric 0).inner x v v = 1)
    (hw : (F.metric 0).inner x w w = 1)
    (hvw : (F.metric 0).inner x v w = 0)
    (hzero : (F.connection 0).curvatureTensor x v w v w = 0) :
    ∀ y, (F.connection 0).scalarCurvature y = 1 := by
  obtain ⟨hc, hcard, hgeom⟩ := exists_complete_nullCover_coordinate hC F
    hoperator hnonflat hcomplete f hf hsol x v w hv hw hvw hzero
  let := unitRicciKernelChartedSpace (F.connection 0) hc
  let := unitRicciKernelIsManifold (F.connection 0) hc
  let := unitRicciKernelT3Space (F.connection 0) hc
  let L := unitRicciKernelFlow F hc
  let r := unitRicciKernelCoordinate (F.connection 0) f
  obtain ⟨hc0, hr, hu, hz, _⟩ := hgeom
  intro y
  have hne : (unitRicciKernelProjection (F.connection 0) ⁻¹' {y}).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by
      change Nat.card (unitRicciKernelProjection (F.connection 0) ⁻¹' {y}) ≠ 0
      rw [hcard y]
      norm_num)
  obtain ⟨p, hp⟩ := hne
  change unitRicciKernelProjection (F.connection 0) p = y at hp
  let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin 3)) p
  let H := L.restrictComponent p
  let projection : C → M := fun q => unitRicciKernelProjection (F.connection 0) q.1
  obtain ⟨hconn, hcC, hrC, huC, hzC⟩ :=
    connectedComponent_complete_parallel_coordinate (L.connection 0) hr hu hz hc0 p
  let : ConnectedSpace C := hconn
  have hsurj := unitRicciKernelComponent_projection_surjective
    (F.connection 0) hc hcard p
  have hπ : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ projection :=
    unitRicciKernelComponent_projection_isLocalDiffeomorph (F.connection 0) hc p
  have hmetric (q : C) (a b : TangentSpace (𝓡 3) q) :
      (H.metric 0).inner q a b = (F.metric 0).inner (projection q)
        (mfderiv (𝓡 3) (𝓡 3) projection q a)
        (mfderiv (𝓡 3) (𝓡 3) projection q b) := by
    change _ = (F.metric 0).inner (projection q)
      (mfderiv (𝓡 3) (𝓡 3)
        (unitRicciKernelProjection (F.connection 0) ∘ Subtype.val) q a)
      (mfderiv (𝓡 3) (𝓡 3)
        (unitRicciKernelProjection (F.connection 0) ∘ Subtype.val) q b)
    rw [mfderiv_comp q
      ((unitRicciKernelProjection_isLocalDiffeomorph
        (F.connection 0) hc).mdifferentiable (by simp) q.1)
      ((Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) C).mdifferentiable (by simp) q)]
    rfl
  have hφ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) 2 (f ∘ projection) :=
    hf.comp (hπ.contMDiff.of_le (by norm_cast : (2 : ℕ∞ω) ≤ ∞))
  have hsolC (q : C) (a b : TangentSpace (𝓡 3) q) :
      (H.connection 0).ricci q a b +
        (H.connection 0).hessian (f ∘ projection) q a b =
          (1 / 2 : ℝ) * (H.metric 0).inner q a b := by
    rw [(H.connection 0).ricci_eq_of_local_isometry (F.connection 0)
      isOpen_univ hπ.contMDiff.contMDiffOn (fun q _ => hmetric q) (mem_univ q),
      (H.connection 0).hessian_comp_of_metric_pullback_of_C2 (F.connection 0)
        (hπ.contMDiff q)
        (Eventually.of_forall fun z => ⟨hπ.mfderivToContinuousLinearEquiv (by simp) z, rfl⟩)
        (Eventually.of_forall hmetric) (hf (projection q)), hmetric]
    exact hsol (projection q) _ _
  have hopC (q : C) : (H.connection 0).NonnegativeCurvatureOperator q :=
    (L.restrictComponent_nonnegativeCurvatureOperator_iff p 0 q).mpr
      ((unitRicciKernelFlow_nonnegativeCurvatureOperator_iff F hc 0 q.1).mpr
        (hoperator 0 le_rfl _))
  have hnC : ∃ q : C, (H.connection 0).curvatureTensorNorm q ≠ 0 := by
    obtain ⟨z, hz⟩ := hnonflat
    obtain ⟨q, hq⟩ := hsurj z
    change unitRicciKernelProjection (F.connection 0) q.1 = z at hq
    refine ⟨q, ?_⟩
    rw [L.restrictComponent_curvatureTensorNorm p 0 q,
      unitRicciKernelFlow_curvatureTensorNorm, hq]
    exact hz
  let q : C := ⟨p, mem_connectedComponent⟩
  have hs := scalarCurvature_eq_twice_scale_of_parallel_soliton
    (H.connection 0) hcC hrC huC hzC hφ (by norm_num : (0 : ℝ) < 1 / 2)
    hsolC hopC hnC q
  rw [L.restrictComponent_scalarCurvature p 0 q,
    unitRicciKernelFlow_scalarCurvature] at hs
  change (F.connection 0).scalarCurvature
    (unitRicciKernelProjection (F.connection 0) p) = 2 * (1 / 2) at hs
  simpa only [hp, mul_one_div_cancel (by norm_num : (2 : ℝ) ≠ 0)] using hs

end PoincareConjecture.RicciFlow
