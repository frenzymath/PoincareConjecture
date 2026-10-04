import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Limit.Canonical.LimitCanonicalFamilyChartJets
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Lifetime.CanonicalGeometry.CapPersistenceNeckSets

/-!
# One compact-time jet tail on the whole captured neck

The actual compact ambient cover precedes every time, sphere center,
axial point and derivative order. MT Proposition 17.1, pp. 407-408;
limit-canonical-neck-family-jets.md, C.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M47

open M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {V : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (G : GeneralizedBlowupConvergence V J)

private local instance : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance : ChartedSpace E₃ G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold

/-- The whole old neck has one full-order native metric-jet estimate
over every included time in the actual compact time set. -/
theorem limitCanonical_eventually_neck_family_metric_jets
    (P : M47Predecessors.{u}) (N : EpsilonNeck (G.limit.flow.metric 0))
    (m : ℕ) (hm : m ≤ Nat.floor N.epsilon⁻¹)
    {Ktime : Set ℝ} (hKtime : IsCompact Ktime) (hKJ : Ktime ⊆ J)
    {K : Set G.limit.sliceCarrier.carrier} (hK : IsCompact K) (hNK : N.carrier ⊆ K)
    {rho : ℝ} (hrho : 0 < rho) :
    ∀ᶠ k in atTop, Ktime ⊆ Icc (-G.exhaustion.time k) 0 ∧
      K ⊆ G.exhaustion.space k ∧
      ∀ s ∈ Ktime, ∀ (q : UnitTwoSphere) (z : ℝ),
        z ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
        ∀ j ≤ m, ∀ i l : Fin 3,
          ‖iteratedFDeriv ℝ j (fun y =>
            roundCylinderTensorCoefficient
                (generalizedCylinderPullback (G.embedding k) N.coordinate_map s)
                (chartAt E₂ q) y i l -
              roundCylinderTensorCoefficient
                (roundCylinderPullback (G.limit.flow.metric s) N.coordinate_map)
                (chartAt E₂ q) y i l) (0, z)‖ < rho := by
  classical
  let B (k : ℕ) (s : ℝ) (q : UnitTwoSphere) (z : ℝ) : Prop :=
    ∀ j ≤ m, ∀ i l : Fin 3,
      ‖iteratedFDeriv ℝ j (fun y =>
        roundCylinderTensorCoefficient
            (generalizedCylinderPullback (G.embedding k) N.coordinate_map s)
            (chartAt E₂ q) y i l -
          roundCylinderTensorCoefficient
            (roundCylinderPullback (G.limit.flow.metric s) N.coordinate_map)
            (chartAt E₂ q) y i l) (0, z)‖ < rho
  have hlocal (a : G.limit.sliceCarrier.carrier) :
      ∃ U : Set G.limit.sliceCarrier.carrier, U ∈ 𝓝 a ∧
        ∀ᶠ k in atTop, ∀ s ∈ Ktime, ∀ (q : UnitTwoSphere) (z : ℝ),
          z ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
          N.coordinate_map (q, z) ∈ U → B k s q z := by
    let c := extChartAt (𝓡 3) a
    obtain ⟨H, hH, haH, hHt⟩ := exists_compact_subset
      (isOpen_extChartAt_target (I := 𝓡 3) a) (mem_extChartAt_target (I := 𝓡 3) a)
    let U := c.source ∩ c ⁻¹' H
    have hU : U ∈ 𝓝 a := inter_mem (extChartAt_source_mem_nhds (I := 𝓡 3) a)
      ((continuousAt_extChartAt (I := 𝓡 3) a).preimage_mem_nhds
        (mem_interior_iff_mem_nhds.mp haH))
    refine ⟨U, hU, ?_⟩
    filter_upwards [limitCanonical_eventually_chart_neck_family_jets G P N m hm
      hKtime hKJ a hH hHt hrho] with k hk s hs q z hz hx
    exact hk.2 s hs q z hz hx.1 hx.2
  choose U hU hbound using hlocal
  obtain ⟨S, _hS, hcover⟩ := hK.elim_nhds_subcover U (fun a _ => hU a)
  obtain ⟨j0, hj0⟩ := G.exists_exhaustion_superset hK
  filter_upwards [S.eventually_all.mpr (fun a _ => hbound a),
    G.exhaustion.time_cofinal Ktime hKtime hKJ, eventually_ge_atTop j0]
    with k hk htime hjk
  refine ⟨htime, hj0.trans (G.exhaustion.space_increasing hjk), ?_⟩
  intro s hs q z hz
  obtain ⟨a, haS, hxa⟩ : ∃ a ∈ S, N.coordinate_map (q, z) ∈ U a := by
    simpa only [mem_iUnion, exists_prop] using hcover (hNK (N.coordinate_map_mem_of_axial_mem hz))
  exact hk a haS s hs q z hz hxa

end PoincareMT.M47
