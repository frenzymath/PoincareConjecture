import PoincareLib.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.OpenBalls
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.MetricBalls
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Calibration
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Component.Reference
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Metric.CompactComparison
import PoincareLib.Geometry.Riemannian.Metric.Diffeomorph

/-!
# Comparison of captured old cap-core balls

The old core ball transports exactly to the intrinsic restricted old metric.
Uniform metric comparison on the compact capture set then gives both terminal
ball inclusions by path confinement, rather than assuming them as data.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

/-- Every old metric ball contained in the regular region is exactly the
intrinsic ball for the old-time metric on the terminal carrier. -/
theorem regularReferencePreimage_ball_eq
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (t : ℝ) (ht : t ∈ Ico H.reference.tMinus T)
    (x : H.regularRegion P04) (r : ℝ)
    (hregular : H.reference.inverse t ht ''
      (F.metric t).ball (H.reference.forward t ht x) r ⊆ H.reference.regularLimitSet) :
    H.regularReferencePreimage P04 t ht
      ((F.metric t).ball (H.reference.forward t ht x) r) =
      ((H.terminalFlow P04).metric t).ball x r := by
  have hdist (z : M) : (H.reference.flow.metric t).edist (x : M) z =
      (F.metric t).edist (H.reference.forward t ht x) (H.reference.forward t ht z) :=
    RiemannianMetric.edist_diffeomorph _ _ (H.reference.sliceDiffeomorph t ht)
      (fun a v w => (H.reference.metric_pullback t ht a v w).symm) x z
  have hball : (H.reference.flow.metric t).ball (x : M) r ⊆ H.regularRegion P04 := by
    intro z hz
    apply hregular
    refine ⟨H.reference.forward t ht z, ?_, H.reference.left_inverse t ht z⟩
    change (F.metric t).edist (H.reference.forward t ht x)
      (H.reference.forward t ht z) < ENNReal.ofReal r
    rwa [← hdist z]
  rw [H.terminalFlow_metric_of_lt P04 ht.2,
    RiemannianMetric.ball_subtype_val_of_subset _ _
      (H.reference.flow.restrictToOpen_inner (H.regularRegion P04) t) x r hball]
  ext z
  change (F.metric t).edist (H.reference.forward t ht x)
      (H.reference.forward t ht z) < ENNReal.ofReal r ↔
    (H.reference.flow.metric t).edist (x : M) (z : M) < ENNReal.ofReal r
  rw [hdist]

/-- Both terminal ball inclusions follow eventually from the original cap
certificate and compact carrier capture, with any prescribed factor `c > 1`.
The smaller terminal ball also has compact closure. -/
theorem eventually_cap_core_ball_comparison
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A) {c : ℝ} (hc : 1 < c) :
    ∀ᶠ t in 𝓝[<] T, ∀ ht : t ∈ Ico H.reference.tMinus T,
      ∀ N : CapCertificate (F.metric t),
      H.reference.inverse t ht '' N.carrier ⊆ Subtype.val '' A →
      ∀ x : H.regularRegion P04, H.reference.forward t ht x ∈ N.core →
      let r := N.core_radius (H.reference.forward t ht x)
      let S := H.regularReferencePreimage P04 t ht
        ((F.metric t).ball (H.reference.forward t ht x) r)
      (H.terminalMetric P04).ball x (r / c) ⊆ S ∧
      S ⊆ (H.terminalMetric P04).ball x (c * r) ∧
      IsCompact (closure ((H.terminalMetric P04).ball x (r / c))) := by
  have hcpos : 0 < c := zero_lt_one.trans hc
  filter_upwards [H.eventually_terminal_tangentNorm_comparison P04 hA hc] with t hnorm
  intro ht N hcapture x hx
  dsimp only
  let r := N.core_radius (H.reference.forward t ht x)
  let B := (F.metric t).ball (H.reference.forward t ht x) r
  have hr : 0 < r := N.core_radius_pos _ hx
  have hBN : B ⊆ N.carrier := fun z hz => N.core_ball_subset _ hx (subset_closure hz)
  have hBcapture : H.reference.inverse t ht '' B ⊆ Subtype.val '' A :=
    (image_mono hBN).trans hcapture
  have hBregular : H.reference.inverse t ht '' B ⊆ H.reference.regularLimitSet := by
    rintro z hz
    obtain ⟨a, _, rfl⟩ := hBcapture hz
    exact a.property
  have hballEq := H.regularReferencePreimage_ball_eq P04 t ht x r hBregular
  have hsubset : ((H.terminalFlow P04).metric t).ball x r ⊆ A := by
    rw [← hballEq]
    exact H.regularReferencePreimage_subset P04 t ht B hBcapture
  have hclosed : closure (((H.terminalFlow P04).metric t).ball x r) ⊆ A :=
    closure_minimal hsubset hA.isClosed
  have hcompact : IsCompact (closure (((H.terminalFlow P04).metric t).ball x r)) :=
    hA.of_isClosed_subset isClosed_closure hclosed
  have hclosed' : ∀ z, ((H.terminalFlow P04).metric t).edist x z ≤ ENNReal.ofReal r → z ∈ A := by
    intro z hz
    apply hclosed
    rwa [RiemannianMetric.closure_ball_eq_edist_le _ x hr]
  have hcr : c * (r / c) ≤ r := by rw [mul_div_cancel₀ _ (ne_of_gt hcpos)]
  rw [hballEq]
  exact ⟨RiemannianMetric.ball_subset_ball_of_tangentNorm_le_on_closedBall _ _ x hr hcpos hcr
      (fun z hz v => (hnorm z (hclosed' z hz) v).2),
    RiemannianMetric.ball_subset_ball_of_tangentNorm_le _ _ x r c hcpos
      (fun z hz v => (hnorm z (hsubset hz) v).1),
    RiemannianMetric.isCompact_closure_ball_of_tangentNorm_le_on_closedBall _ _ x hr hcpos hcr
      hcompact (fun z hz v => (hnorm z (hclosed' z hz) v).2)⟩

end PoincareMT.SingularTimeAssumptions
