import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Assembly.PositiveComponents.PositiveSurgeryMetric
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Removal.Terminal.TerminalScalar
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Scalar.Bounds.LocalScalarTransport

/-!
# Scalar continuity across the actual retained surgery interior

Morgan--Tian Lemma 11.2 and Proposition 16.5, used on p. 393.
The actual terminal metric is locally isometric to the retained post
metric. M44's checked preterminal scalar limit therefore has exactly
the post-surgery scalar as its limit; no scalar jump is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.Proofs.M46

variable {g0 : StandardInitialMetric} {K : MetricSurgeryConstants} {P : SurgeryParameters}
  {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}

/-- The retained terminal and post-surgery metrics have the same actual
scalar at every retained interior point, Proposition 16.5, p. 370. -/
theorem retained_scalar_eq_terminal
    (event : SurgeryEventData g0 K P slice metric T)
    (D : LeviCivitaData (metric T))
    {q : (slice event.tMinus).carrier} (hq : q ∈ interior event.retained_pre) :
    D.scalarCurvature (event.retention.map q) =
      event.limit_connection.scalarCurvature (event.limit_identify.map q) := by
  obtain ⟨hU, hf, hm⟩ := retained_terminal_metric_identification event
  let f := event.retention.map ∘ event.limit_identify.inverse
  have hi (y : event.terminal.carrier)
      (hy : y ∈ event.limit_identify.inverse ⁻¹' interior event.retained_pre) :
      (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible := by
    have hb := event.limit_metric.mfderiv_bijective_of_pullback_eq (metric T) y
      (fun u v => (hm y hy u v).symm)
    let : FiniteDimensional ℝ (TangentSpace (𝓡 3) y) := by
      unfold TangentSpace
      infer_instance
    let : FiniteDimensional ℝ (TangentSpace (𝓡 3) (f y)) := by
      unfold TangentSpace
      infer_instance
    let : T2Space (TangentSpace (𝓡 3) y) := by
      unfold TangentSpace
      infer_instance
    let : T2Space (TangentSpace (𝓡 3) (f y)) := by
      unfold TangentSpace
      infer_instance
    exact ⟨(LinearEquiv.ofBijective
      (mfderiv (𝓡 3) (𝓡 3) f y).toLinearMap hb).toContinuousLinearEquiv, rfl⟩
  have hleft := event.limit_identify.left_inverse
    (event.retained_pre_subset (interior_subset hq))
  have hy : event.limit_identify.map q ∈
      event.limit_identify.inverse ⁻¹' interior event.retained_pre := by
    change event.limit_identify.inverse (event.limit_identify.map q) ∈
      interior event.retained_pre
    rwa [hleft]
  have h := (M44.scalar_ricciNormSq_eq_of_local_isometry
    event.limit_connection D hU hf hi hm hy).1
  simpa only [Function.comp_apply, hleft] using h

/-- The preterminal scalar of a retained line converges to its actual
post-surgery scalar, so the one global backward scalar comparison is
continuous at every retained event, pp. 392-393. -/
theorem tendsto_preterminal_scalar_retained
    (event : SurgeryEventData g0 K P slice metric T)
    (D : LeviCivitaData (metric T))
    {q : (slice event.tMinus).carrier} (hq : q ∈ interior event.retained_pre) :
    Tendsto (fun t => (event.pre_flow.connection t).scalarCurvature q) (𝓝[<] T)
      (𝓝 (D.scalarCurvature (event.retention.map q))) := by
  rw [retained_scalar_eq_terminal event D hq]
  exact M44.tendsto_preterminal_scalar event
    (event.retained_pre_subset (interior_subset hq))

end PoincareMT.Proofs.M46
