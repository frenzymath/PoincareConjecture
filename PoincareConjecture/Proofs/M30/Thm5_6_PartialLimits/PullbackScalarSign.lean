import PoincareConjecture.Proofs.M30.Thm5_33.NegativeDefectClosure
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalExtension
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Coordinates.Coefficients
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.LimitCurvature
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Curvature.Conformal.ConformalPinching

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M30

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem scalar_and_nonnegativeCurvatureOperator_of_pullback_metric_jets
    {alpha : Type v} {l : Filter alpha} [l.NeBot]
    {M : alpha → Type u} [∀ i, TopologicalSpace (M i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M i)]
    [∀ i, IsManifold (𝓡 3) ∞ (M i)]
    {gseq : ∀ i, RiemannianMetric 3 (M i)}
    (Dseq : ∀ i, LeviCivitaData (gseq i))
    (phi : ∀ i, EuclideanSpace ℝ (Fin 3) → M i)
    {g : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))}
    (D : LeviCivitaData g) (p : EuclideanSpace ℝ (Fin 3))
    (hphi : ∀ᶠ i in l, ∀ᶠ y in 𝓝 p,
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ (phi i) y ∧
        Function.Injective (mfderiv (𝓡 3) (𝓡 3) (phi i) y))
    (hjets : ∀ r : ℕ, r ≤ 2 → ∀ a b : Fin 3,
      Tendsto (fun i => iteratedFDeriv ℝ r
        (fun y => (gseq i).pullbackCoefficients (phi i) y
          (EuclideanSpace.basisFun (Fin 3) ℝ a)
          (EuclideanSpace.basisFun (Fin 3) ℝ b)) p) l
        (𝓝 (iteratedFDeriv ℝ r
          (fun y => g.inner y (EuclideanSpace.basisFun (Fin 3) ℝ a)
            (EuclideanSpace.basisFun (Fin 3) ℝ b)) p)))
    (hdefect : Tendsto (fun i => (Dseq i).negativeCurvaturePart (phi i p))
      l (𝓝 0)) :
    Tendsto (fun i => (Dseq i).scalarCurvature (phi i p))
      l (𝓝 (D.scalarCurvature p)) ∧
      D.NonnegativeCurvatureOperator p := by
  classical
  have hreal : ∀ᶠ i in l,
      ∃ gd : Σ h : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)), LeviCivitaData h,
        (gd.1.euclideanCoefficients =ᶠ[𝓝 p] (gseq i).pullbackCoefficients (phi i)) ∧
        gd.2.scalarCurvature p = (Dseq i).scalarCurvature (phi i p) ∧
        gd.2.negativeCurvaturePart p = (Dseq i).negativeCurvaturePart (phi i p) := by
    filter_upwards [hphi] with i hi
    obtain ⟨U, hUphi, hU, hpU⟩ := mem_nhds_iff.mp hi
    have hpos : ∀ y ∈ U, ∀ w, w ≠ 0 →
        0 < (gseq i).pullbackCoefficients (phi i) y w w := by
      intro y hy w hw
      apply (gseq i).pos (phi i y)
      intro hz
      apply hw
      apply (hUphi hy).2
      rw [map_zero]
      convert! hz using 1
    obtain ⟨h, Dh, V, hV, hpV, hVU, heq⟩ :=
      RiemannianMetric.exists_local_realization hU hpU
        ((gseq i).pullbackCoefficients (phi i))
        (fun y hy => ((gseq i).contDiffAt_pullbackCoefficients
          (hUphi hy).1).contDiffWithinAt)
        (fun y _ a b => (gseq i).symm (phi i y) _ _) hpos
    have hsmooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (phi i) V :=
      fun y hy => ((hUphi (hVU hy)).1).contMDiffWithinAt
    have hmetric : ∀ y ∈ V, ∀ a b : TangentSpace (𝓡 3) y,
        h.inner y a b = (gseq i).inner (phi i y)
          (mfderiv (𝓡 3) (𝓡 3) (phi i) y a)
          (mfderiv (𝓡 3) (𝓡 3) (phi i) y b) := by
      intro y hy a b
      exact congrArg (fun A => A a b) (heq y hy)
    refine ⟨⟨h, Dh⟩, Filter.Eventually.mono (hV.mem_nhds hpV) heq, ?_, ?_⟩
    · exact Dh.scalarCurvature_eq_of_local_isometry (Dseq i) hV hsmooth hmetric hpV
    · exact MetricSurgery.negativeCurvaturePart_eq_of_local_isometry
        Dh (Dseq i) hV hsmooth hmetric hpV
  obtain ⟨gd, hgd⟩ := hreal.choice
  have hj (r : ℕ) (hr : r ≤ 2) (a b : Fin 3) :
      Tendsto (fun i => iteratedFDeriv ℝ r
        (fun y => (gd i).1.inner y (EuclideanSpace.basisFun (Fin 3) ℝ a)
          (EuclideanSpace.basisFun (Fin 3) ℝ b)) p) l
        (𝓝 (iteratedFDeriv ℝ r
          (fun y => g.inner y (EuclideanSpace.basisFun (Fin 3) ℝ a)
            (EuclideanSpace.basisFun (Fin 3) ℝ b)) p)) := by
    apply (hjets r hr a b).congr'
    filter_upwards [hgd] with i hi
    have heq : (fun y => (gd i).1.inner y (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b)) =ᶠ[𝓝 p]
        (fun y => (gseq i).pullbackCoefficients (phi i) y
          (EuclideanSpace.basisFun (Fin 3) ℝ a)
          (EuclideanSpace.basisFun (Fin 3) ℝ b)) :=
      hi.1.mono (fun y hy => congrArg (fun A =>
        A (EuclideanSpace.basisFun (Fin 3) ℝ a)
          (EuclideanSpace.basisFun (Fin 3) ℝ b)) hy)
    exact ((heq.iteratedFDeriv ℝ r).self_of_nhds).symm
  have hd : Tendsto (fun i => (gd i).2.negativeCurvaturePart p) l (𝓝 0) :=
    hdefect.congr' (hgd.mono fun i hi => hi.2.2.symm)
  have hs := LeviCivitaData.tendsto_scalarCurvature_of_scalar_metric_jets
    (fun i => (gd i).2) D p (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis hj
  refine ⟨hs.congr' (hgd.mono fun i hi => hi.2.1), ?_⟩
  exact nonnegativeCurvatureOperator_of_scalar_metric_jets_of_vanishing_defect
    (fun i => (gd i).2) D p (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis hj hd

end PoincareConjecture.M30
