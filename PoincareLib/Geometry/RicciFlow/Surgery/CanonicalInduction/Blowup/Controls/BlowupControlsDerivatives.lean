import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Generalized.GeneralizedBridgeGeometry
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Positive.PositiveHistoryAnalytics
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Blowup.Caps.CapScalarEstimates

/-!
# Actual generalized scalar derivatives from physical analytics

The spatial local isometries preserve the complete pointwise estimate.
The actual ordinary flow in each generalized box supplies the scalar
within-time derivative on that box's original interval.
Source: Morgan--Tian equation (3.7), p. 41, and Claim 17.9, p. 406.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M47

/-- Physical analytics transfer to the selected regular history at every
included time, including its retained region at an old surgery. -/
theorem regular_history_pointwise_analytic_estimate
    (h04 : RicciFlowCurvatureTheory.{u})
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) {t : ℝ} (ht : t ∈ H.generalized.interval)
    {x : (H.generalized.slice t).carrier} {A : ℝ}
    (h : M45PointwiseAnalyticEstimate (F.metric t) (F.connection t)
      (H.history.forward t ht x) A) :
    M45PointwiseAnalyticEstimate (H.generalized.metric t)
      (H.generalized.connection t) x A := by
  have hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (H.history.forward t ht) := by
    intro y
    exact (regular_history_slice_chart H t ht).isLocalDiffeomorphAt
      (𝓡 3) (𝓡 3) ∞ (mem_univ y)
  exact M47Positive.pointwise_analytic_estimate_of_metric_pullback
    (H.generalized.connection t) (F.connection t)
    (h04.tensor_calculus 3 (F.slice t).carrier (F.metric t) (F.connection t)) hf
    (fun y v w => (H.history.metric_pullback t ht y v w).symm) h

/-- A generalized flow box supplies an actual partial spatial chart at
each included time; no extension of its time interval is involved. -/
noncomputable def generalized_box_slice_chart (G : GeneralizedRicciFlowData.{u})
    (b : G.box_index) (t : ℝ) (ht : t ∈ (G.box b).interval) :
    PartialDiffeomorph (𝓡 3) (𝓡 3)
      (G.box b).carrier.carrier (G.slice t).carrier ∞ where
  toFun := (G.box b).forward t ht
  invFun := (G.box b).inverse t ht
  source := univ
  target := range ((G.box b).forward t ht)
  map_source' x _ := mem_range_self x
  map_target' _ _ := mem_univ _
  left_inv' x _ := (G.box b).left_inverse t ht x
  right_inv' _ hx := (G.box b).right_inverse t ht hx
  open_source := isOpen_univ
  open_target := ((G.box b).forward_openEmbedding t ht).isOpen_range
  contMDiffOn_toFun := ((G.box b).forward_smooth t ht).contMDiffOn
  contMDiffOn_invFun := (G.box b).inverse_smooth t ht

/-- The actual ordinary box scalar equals the selected generalized
scalar at its literal image point. -/
theorem generalized_box_scalar_eq (G : GeneralizedRicciFlowData.{u})
    (b : G.box_index) (t : ℝ) (ht : t ∈ (G.box b).interval)
    (x : (G.box b).carrier.carrier) :
    ((G.box b).flow.connection t).scalarCurvature x =
      G.scalar ⟨t, (G.box b).forward t ht x⟩ := by
  exact ((G.box b).flow.connection t).scalarCurvature_eq_of_local_isometry
    (G.connection t) isOpen_univ ((G.box b).forward_smooth t ht).contMDiffOn
    (fun y _hy v w => ((G.box b).metric_pullback t ht y v w).symm) (mem_univ x)

/-- Spatial local isometry transfers all three pointwise quantities to
the actual ordinary flow of a generalized box at the same coefficient. -/
theorem generalized_box_pointwise_analytic_estimate
    (h04 : RicciFlowCurvatureTheory.{u}) (G : GeneralizedRicciFlowData.{u})
    (b : G.box_index) (t : ℝ) (ht : t ∈ (G.box b).interval)
    {x : (G.box b).carrier.carrier} {A : ℝ}
    (h : M45PointwiseAnalyticEstimate (G.metric t) (G.connection t)
      ((G.box b).forward t ht x) A) :
    M45PointwiseAnalyticEstimate ((G.box b).flow.metric t)
      ((G.box b).flow.connection t) x A := by
  have hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ ((G.box b).forward t ht) := by
    intro y
    exact (generalized_box_slice_chart G b t ht).isLocalDiffeomorphAt
      (𝓡 3) (𝓡 3) ∞ (mem_univ y)
  exact M47Positive.pointwise_analytic_estimate_of_metric_pullback
    ((G.box b).flow.connection t) (G.connection t)
    (h04.tensor_calculus 3 (G.slice t).carrier (G.metric t) (G.connection t)) hf
    (fun y v w => ((G.box b).metric_pullback t ht y v w).symm) h

/-- The actual scalar evolution equation supplies the bounded within
derivative on the box's original interval, including relative endpoints. -/
theorem generalized_box_scalar_time_bound
    (h04 : RicciFlowCurvatureTheory.{u}) (G : GeneralizedRicciFlowData.{u})
    (b : G.box_index) (t : ℝ) (ht : t ∈ (G.box b).interval)
    {x : (G.box b).carrier.carrier} {A : ℝ}
    (h : M45PointwiseAnalyticEstimate (G.metric t) (G.connection t)
      ((G.box b).forward t ht x) A) :
    ∃ d : ℝ, HasDerivWithinAt
        (fun s => ((G.box b).flow.connection s).scalarCurvature x) d
        (G.box b).interval t ∧
      |d| ≤ A * ((G.box b).flow.connection t).scalarCurvature x ^ 2 := by
  have hbox := generalized_box_pointwise_analytic_estimate h04 G b t ht h
  exact ⟨_, h04.scalar_evolution 3 (G.box b).carrier.carrier (G.box b).interval
    (G.box b).flow t ht x, hbox.2.2⟩

/-- The literal scalar-gradient supremum controls every actual
metric-unit directional derivative with the same coefficient. -/
theorem generalized_scalar_directional_bound (G : GeneralizedRicciFlowData.{u})
    (t : ℝ) {x : (G.slice t).carrier} {A : ℝ}
    (h : M45PointwiseAnalyticEstimate (G.metric t) (G.connection t) x A)
    (v : TangentSpace (𝓡 3) x) (hv : (G.metric t).inner x v v = 1) :
    |mvfderiv (𝓡 3) (fun y => G.scalar ⟨t, y⟩) x v| ≤
      A * G.scalar ⟨t, x⟩ ^ (3 / 2 : ℝ) :=
  ((G.connection t).abs_scalar_directional_le_scalarGradientNorm x v hv).trans h.2.1

end PoincareMT.M47
