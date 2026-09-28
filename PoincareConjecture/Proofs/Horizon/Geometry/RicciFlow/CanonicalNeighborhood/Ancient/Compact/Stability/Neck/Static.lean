import PoincareConjecture.Proofs.Ch01.CurvatureConnection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.Comparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Scalar.Terminal









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace

namespace M23InteriorConvergence

variable {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
  (G : M23InteriorConvergence S)
  (e : ∀ j, NormalizedKappaSpacetimeEmbedding
    (source := S.term (G.subsequence j)) (target := G.limit) (Iic 0 ×ˢ G.exhaustion j))



theorem terminalNeck_scalar_comparison
    (N : EpsilonNeck (G.limit.flow.flow.metric 0)) :
    RoundCylinderClose N.epsilon 0 (fun z v w =>
      (G.limit.flow.flow.connection 0).scalarCurvature N.center *
        roundCylinderPullback (G.limit.flow.flow.metric 0) N.coordinate_map z v w) := by
  have h := N.metric_comparison.close
  have hpow : N.scale⁻¹ ^ 2 = (G.limit.flow.flow.connection 0).scalarCurvature N.center := by
    rw [N.scale_eq_scalar, ← N.connection.scalarCurvature_eq (G.limit.flow.flow.connection 0),
      neg_div, Real.rpow_neg N.scalar_center_pos.le, inv_inv, ← Real.rpow_natCast,
      ← Real.rpow_mul N.scalar_center_pos.le]
    norm_num
  simpa only [hpow] using h



def terminalStaticNeck (N : EpsilonNeck (G.limit.flow.flow.metric 0))
    {ε : ℝ} (hεpos : 0 < ε) (hεhalf : ε < 1 / 2) (k : ℕ)
    (hsource : (G.terminalNeckEmbedding e N ε k).source = univ ×ˢ Ioo (-ε⁻¹) ε⁻¹)
    (hR : 0 < ((S.term (G.subsequence k)).flow.flow.connection 0).scalarCurvature
      ((e k).toFun (0, N.center)).2)
    (hclose : RoundCylinderClose ε 0 (fun z v w =>
      ((S.term (G.subsequence k)).flow.flow.connection 0).scalarCurvature
        ((e k).toFun (0, N.center)).2 *
      roundCylinderPullback ((S.term (G.subsequence k)).flow.flow.metric 0)
        (G.terminalNeckEmbedding e N ε k) z v w)) :
    EpsilonNeck ((S.term (G.subsequence k)).flow.flow.metric 0) := by
  let f := G.terminalNeckEmbedding e N ε k
  have hcoords := G.terminalNeckEmbedding_coordinates_of_source e N hεpos k hsource
  exact {
    epsilon := ε
    epsilon_pos := hεpos
    epsilon_lt_half := hεhalf
    scale := (((S.term (G.subsequence k)).flow.flow.connection 0).scalarCurvature
      ((e k).toFun (0, N.center)).2) ^ (-1 / 2 : ℝ)
    scale_pos := Real.rpow_pos_of_pos hR _
    center := ((e k).toFun (0, N.center)).2
    connection := (S.term (G.subsequence k)).flow.flow.connection 0
    scalar_center_pos := hR
    scale_eq_scalar := rfl
    carrier := f.target
    carrier_open := f.open_target
    coordinate := neckDomainCoordinates f hsource
    coordinate_map := f
    coordinate_map_eq := fun z => rfl
    coordinate_map_smooth := hcoords.1
    coordinate_inverse := f.symm
    coordinate_inverse_mem := fun x hx => neckDomainCoordinates_inverse_mem f hsource hx
    coordinate_inverse_left := neckDomainCoordinates_inverse_left f hsource
    coordinate_inverse_right := neckDomainCoordinates_inverse_right f hsource
    coordinate_inverse_smooth := hcoords.2.1
    central_sphere := f '' (univ ×ˢ ({0} : Set ℝ))
    central_sphere_eq := rfl
    center_on_central_sphere := G.terminalNeckEmbedding_center_mem_central_image e N ε k
    central_sphere_subset := hcoords.2.2
    metric_comparison := ⟨by
      have hpow :
          ((((S.term (G.subsequence k)).flow.flow.connection 0).scalarCurvature
            ((e k).toFun (0, N.center)).2) ^ (-1 / 2 : ℝ))⁻¹ ^ 2 =
          ((S.term (G.subsequence k)).flow.flow.connection 0).scalarCurvature
            ((e k).toFun (0, N.center)).2 := by
        rw [neg_div, Real.rpow_neg hR.le, inv_inv, ← Real.rpow_natCast,
          ← Real.rpow_mul hR.le]
        norm_num
      simpa only [hpow] using hclose⟩ }

variable (N : EpsilonNeck (G.limit.flow.flow.metric 0))
  {ε : ℝ} (hεpos : 0 < ε) (hεhalf : ε < 1 / 2) (k : ℕ)
  (hsource : (G.terminalNeckEmbedding e N ε k).source = univ ×ˢ Ioo (-ε⁻¹) ε⁻¹)
  (hR : 0 < ((S.term (G.subsequence k)).flow.flow.connection 0).scalarCurvature
    ((e k).toFun (0, N.center)).2)
  (hclose : RoundCylinderClose ε 0 (fun z v w =>
    ((S.term (G.subsequence k)).flow.flow.connection 0).scalarCurvature
      ((e k).toFun (0, N.center)).2 *
    roundCylinderPullback ((S.term (G.subsequence k)).flow.flow.metric 0)
      (G.terminalNeckEmbedding e N ε k) z v w))

@[simp] theorem terminalStaticNeck_epsilon :
    (G.terminalStaticNeck e N hεpos hεhalf k hsource hR hclose).epsilon = ε := rfl

@[simp] theorem terminalStaticNeck_center :
    (G.terminalStaticNeck e N hεpos hεhalf k hsource hR hclose).center =
      ((e k).toFun (0, N.center)).2 := rfl

@[simp] theorem terminalStaticNeck_scale :
    (G.terminalStaticNeck e N hεpos hεhalf k hsource hR hclose).scale =
      (((S.term (G.subsequence k)).flow.flow.connection 0).scalarCurvature
        ((e k).toFun (0, N.center)).2) ^ (-1 / 2 : ℝ) := rfl

@[simp] theorem terminalStaticNeck_connection :
    (G.terminalStaticNeck e N hεpos hεhalf k hsource hR hclose).connection =
      (S.term (G.subsequence k)).flow.flow.connection 0 := rfl

@[simp] theorem terminalStaticNeck_coordinate_map :
    (G.terminalStaticNeck e N hεpos hεhalf k hsource hR hclose).coordinate_map =
      G.terminalNeckEmbedding e N ε k := rfl

@[simp] theorem terminalStaticNeck_coordinate_inverse :
    (G.terminalStaticNeck e N hεpos hεhalf k hsource hR hclose).coordinate_inverse =
      (G.terminalNeckEmbedding e N ε k).symm := rfl

theorem terminalStaticNeck_central_sphere :
    (G.terminalStaticNeck e N hεpos hεhalf k hsource hR hclose).central_sphere =
      (fun x => ((e k).toFun (0, x)).2) '' N.central_sphere :=
  G.terminalNeckEmbedding_central_sphere_image e N ε k

theorem terminalStaticNeck_carrier :
    (G.terminalStaticNeck e N hεpos hεhalf k hsource hR hclose).carrier =
      (fun x => ((e k).toFun (0, x)).2) '' N.region (-ε⁻¹) ε⁻¹ :=
  G.terminalNeckEmbedding_target_eq_image_region e N k hsource

theorem terminalStaticNeck_carrier_of_epsilon_eq (hε : N.epsilon = ε)
    (hN : N.carrier ⊆ G.exhaustion k) :
    (G.terminalStaticNeck e N hεpos hεhalf k hsource hR hclose).carrier =
      (fun x => ((e k).toFun (0, x)).2) '' N.carrier := by
  subst ε
  exact G.terminalNeckEmbedding_full_target e N k hN



theorem terminalStaticNeck_region_of_epsilon_eq (hε : N.epsilon = ε)
    (hN : N.carrier ⊆ G.exhaustion k) (a b : ℝ) :
    (G.terminalStaticNeck e N hεpos hεhalf k hsource hR hclose).region a b =
      (fun x => ((e k).toFun (0, x)).2) '' N.region a b := by
  subst ε
  exact G.terminalNeckEmbedding_full_region e N k hN a b

end M23InteriorConvergence

namespace M23TerminalMetricConvergence

variable {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
  {G : M23InteriorConvergence S}
  {e : ∀ j, NormalizedKappaSpacetimeEmbedding
    (source := S.term (G.subsequence j)) (target := G.limit) (Iic 0 ×ˢ G.exhaustion j)}

theorem eventually_terminalNeck_center_scalar_pos
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (t : ℝ), t ≤ 0 → ∀ x ∈ G.exhaustion k,
      ((e k).toFun (t, x)).2 = ((e k).toFun (0, x)).2)
    (N : EpsilonNeck (G.limit.flow.flow.metric 0)) :
    ∀ᶠ k in atTop,
      0 < ((S.term (G.subsequence k)).flow.flow.connection 0).scalarCurvature
        ((e k).toFun (0, N.center)).2 := by
  have hR : 0 < (G.limit.flow.flow.connection 0).scalarCurvature N.center := by
    rw [← N.connection.scalarCurvature_eq (G.limit.flow.flow.connection 0)]
    exact N.scalar_center_pos
  have hc := (hconv.tendsto_terminal_scalarCurvature_prod hfixed N.center).comp
    (tendsto_id.prodMk tendsto_const_nhds)
  exact hc.eventually (lt_mem_nhds hR)



theorem eventually_terminalStaticNeck
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (s t : ℝ) (x : G.limit.carrier.carrier),
      s ≤ 0 → t ≤ 0 → x ∈ G.exhaustion k →
        ((e k).toFun (s, x)).2 = ((e k).toFun (t, x)).2)
    (N : EpsilonNeck (G.limit.flow.flow.metric 0))
    {ε : ℝ} (hε : N.epsilon < ε) (hεhalf : ε < 1 / 2) :
    ∀ᶠ k in atTop,
      ∃ N' : EpsilonNeck ((S.term (G.subsequence k)).flow.flow.metric 0),
        N'.epsilon = ε ∧
        N'.center = ((e k).toFun (0, N.center)).2 ∧
        N'.scale = (((S.term (G.subsequence k)).flow.flow.connection 0).scalarCurvature
          ((e k).toFun (0, N.center)).2) ^ (-1 / 2 : ℝ) ∧
        N'.connection = (S.term (G.subsequence k)).flow.flow.connection 0 ∧
        N'.coordinate_map = (fun z => ((e k).toFun (0, N.coordinate_map z)).2) ∧
        N'.coordinate_inverse = (fun x => N.coordinate_inverse ((e k).inverse (0, x)).2) ∧
        N'.central_sphere = (fun x => ((e k).toFun (0, x)).2) '' N.central_sphere ∧
        N'.carrier = (fun x => ((e k).toFun (0, x)).2) '' N.region (-ε⁻¹) ε⁻¹ := by
  have hclose := hconv.eventually_terminalCylinder_scalarClose hfixed N.epsilon_pos hε
    N.coordinate_map_smooth N.center (G.terminalNeck_scalar_comparison N)
  have hpos := hconv.eventually_terminalNeck_center_scalar_pos
    (fun k t ht x hx => hfixed k t 0 x ht le_rfl hx) N
  filter_upwards [G.eventually_terminalNeckEmbedding e N hε, hclose, hpos]
    with k hcoords hclose hR
  let N' := G.terminalStaticNeck e N (N.epsilon_pos.trans hε) hεhalf k hcoords.1 hR hclose
  refine ⟨N', rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact G.terminalStaticNeck_central_sphere e N (N.epsilon_pos.trans hε)
      hεhalf k hcoords.1 hR hclose
  · exact G.terminalStaticNeck_carrier e N (N.epsilon_pos.trans hε)
      hεhalf k hcoords.1 hR hclose

end M23TerminalMetricConvergence

end PoincareConjecture
