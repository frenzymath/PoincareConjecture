import PoincareConjecture.Proofs.M47.LimitCanonicalComponentCurvature
import PoincareConjecture.Proofs.M47.ComponentEstimateGeometry
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {V : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (G : GeneralizedBlowupConvergence V J)

private local instance : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance : ChartedSpace E G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold

theorem limitCanonical_component_scalar_convergence
    (P : M47Predecessors.{u}) (F : ℕ → SurgeryFlowData.{u})
    (R : ∀ i, M33RegularHistoryRealization (V.flow i) (F i))
    (hcompact : IsCompact (univ : Set G.limit.sliceCarrier.carrier))
    (a : ℝ) (hsec : ∀ x : G.limit.sliceCarrier.carrier,
      ∀ u v : TangentSpace (𝓡 3) x,
        LeviCivitaData.IsOrthonormalPair (G.limit.flow.metric 0) x u v →
          a < (G.limit.flow.connection 0).sectionalCurvature x u v) :
    TendstoUniformlyOn (fun k x =>
      (M13.scaleLeviCivitaData ((F (G.subsequence k)).connection
        ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
        (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))).scalarCurvature
          (limitCanonicalPhysicalTerminalChart G F R k x))
      (G.limit.flow.connection 0).scalarCurvature atTop univ := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eta heta
  filter_upwards [limitCanonical_component_eventually_physical_curvature
    G P F R hcompact a hsec heta] with k hk x _hx
  rw [Real.dist_eq, abs_sub_comm]
  exact (hk.2.2 x).2.2

theorem limitCanonical_component_scalar_radius_convergence
    (P : M47Predecessors.{u}) (F : ℕ → SurgeryFlowData.{u})
    (R : ∀ i, M33RegularHistoryRealization (V.flow i) (F i))
    (hcompact : IsCompact (univ : Set G.limit.sliceCarrier.carrier))
    {a : ℝ} (ha : 0 < a) (hsec : ∀ x : G.limit.sliceCarrier.carrier,
      ∀ u v : TangentSpace (𝓡 3) x,
        LeviCivitaData.IsOrthonormalPair (G.limit.flow.metric 0) x u v →
          a < (G.limit.flow.connection 0).sectionalCurvature x u v) :
    TendstoUniformlyOn (fun k x =>
      (M13.scaleLeviCivitaData ((F (G.subsequence k)).connection
        ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
        (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))).scalarCurvature
          (limitCanonicalPhysicalTerminalChart G F R k x) ^ (-1 / 2 : ℝ))
      (fun x => (G.limit.flow.connection 0).scalarCurvature x ^ (-1 / 2 : ℝ))
      atTop univ := by
  let : CompactSpace G.limit.carrier.carrier := isCompact_univ_iff.mp hcompact
  let R0 := scalarCurvatureSup (G.limit.flow.metric 0) (G.limit.flow.connection 0)
  let r0 := (G.limit.flow.connection 0).scalarCurvature
  let r : ℕ → G.limit.sliceCarrier.carrier → ℝ := fun k x =>
    (M13.scaleLeviCivitaData ((F (G.subsequence k)).connection
      ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
      (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))).scalarCurvature
        (limitCanonicalPhysicalTerminalChart G F R k x)
  have hbounded : BddAbove (range r0) :=
    (isCompact_range
      (M34.contMDiff_scalarCurvature (G.limit.flow.connection 0)).continuous).bddAbove
  have hupper (x : G.limit.sliceCarrier.carrier) : r0 x ≤ R0 :=
    le_csSup hbounded (mem_range_self x)
  have hlower (x : G.limit.sliceCarrier.carrier) : 6 * a < r0 x :=
    six_mul_lt_scalar_of_sectional_lower (G.limit.flow.connection 0) x a (hsec x)
  have hinterval (x : G.limit.sliceCarrier.carrier) (_hx : x ∈ (univ : Set _)) :
      r0 x ∈ Icc (3 * a) (R0 + 1) := by
    constructor
    · linarith [hlower x]
    · linarith [hupper x]
  have heventual : ∀ᶠ k in atTop, ∀ x ∈ (univ : Set G.limit.sliceCarrier.carrier),
      r k x ∈ Icc (3 * a) (R0 + 1) := by
    filter_upwards [limitCanonical_component_eventually_physical_curvature
      G P F R hcompact a hsec zero_lt_one] with k hk x _hx
    have hl : 6 * a ≤ r k x := (hk.2.2 x).2.1
    have he : |r k x - r0 x| < 1 := (hk.2.2 x).2.2
    exact ⟨by linarith, by linarith [(abs_lt.mp he).2, hupper x]⟩
  have hcontinuous : ContinuousOn (fun s : ℝ => s ^ (-1 / 2 : ℝ))
      (Icc (3 * a) (R0 + 1)) :=
    continuousOn_id.rpow_const (by
      intro x hx
      left
      change x ≠ 0
      linarith [hx.1])
  exact UniformContinuousOn.comp_tendstoUniformlyOn_eventually heventual hinterval
    (isCompact_Icc.uniformContinuousOn_of_continuous hcontinuous)
    (limitCanonical_component_scalar_convergence G P F R hcompact a hsec)

end PoincareConjecture.M47
