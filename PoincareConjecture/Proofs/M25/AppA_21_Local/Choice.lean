import PoincareConjecture.Statements.Ch09.NeckCapTopology
import PoincareConjecture.Proofs.M25.AppA_1_Necks.OverlapSlab
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Uniqueness
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Order.Lattice.Nat
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M}

noncomputable def CapCertificate.exteriorEDepth (C : CapCertificate g) (x : M) :
    ℝ≥0∞ :=
  ⨅ y ∈ C.carrierᶜ, g.edist x y

theorem CapCertificate.m25_core_subset_carrier (C : CapCertificate g) :
    C.core ⊆ C.carrier := by
  rw [C.core_eq_interior_closed_core]
  exact interior_subset.trans (by rw [C.closed_core_eq_complement_end]; exact sdiff_subset)

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in
private theorem scalarCurvature_eq_of_metric
    (D D' : LeviCivitaData g) (x : M) :
    D.scalarCurvature x = D'.scalarCurvature x := by
  unfold LeviCivitaData.scalarCurvature LeviCivitaData.ricci
  simp_rw [D.horizon_curvatureTensor_eq D' x]

theorem CapCertificate.scalarCurvatureSupOn_bounds (C : CapCertificate g)
    {x : M} (hx : x ∈ C.carrier) :
    C.connection.scalarCurvature x ≤ scalarCurvatureSupOn g C.connection C.carrier ∧
      scalarCurvatureSupOn g C.connection C.carrier <
        C.cap_constant * C.connection.scalarCurvature x := by
  obtain ⟨b, hb, hratio⟩ := C.scalar_ratio
  let S : Set ℝ := range (fun y : C.carrier => C.connection.scalarCurvature y)
  have hxS : C.connection.scalarCurvature x ∈ S := ⟨⟨x, hx⟩, rfl⟩
  have hbound : ∀ r ∈ S, r ≤ b * C.connection.scalarCurvature x := by
    rintro r ⟨y, rfl⟩
    exact hratio x hx y y.property
  change C.connection.scalarCurvature x ≤ sSup S ∧
    sSup S < C.cap_constant * C.connection.scalarCurvature x
  refine ⟨le_csSup ⟨_, hbound⟩ hxS, (csSup_le ⟨_, hxS⟩ hbound).trans_lt ?_⟩
  exact mul_lt_mul_of_pos_right hb (C.scalar_pos x hx)

theorem CapCertificate.intrinsicDiameter_lt_of_mem (C : CapCertificate g)
    {x : M} (hx : x ∈ C.carrier) {B : ℝ} (hCB : C.cap_constant ≤ B) :
    intrinsicDiameter g C.carrier <
      ENNReal.ofReal (B * (C.connection.scalarCurvature x) ^ (-1 / 2 : ℝ)) := by
  have hQ := C.scalar_pos x hx
  have hpow := Real.rpow_le_rpow_of_nonpos hQ
    (C.scalarCurvatureSupOn_bounds hx).1 (by norm_num : (-1 / 2 : ℝ) ≤ 0)
  refine C.intrinsic_diameter_bound.trans_le (ENNReal.ofReal_le_ofReal ?_)
  exact (mul_le_mul_of_nonneg_left hpow C.cap_constant_pos.le).trans
    (mul_le_mul_of_nonneg_right hCB (Real.rpow_pos_of_pos hQ _).le)

theorem CapCertificate.exteriorEDepth_pos_le_intrinsicDiameter
    (C : CapCertificate g) {x : M} (hx : x ∈ C.carrier)
    (hproper : ¬ connectedComponent x ⊆ C.carrier) :
    0 < C.exteriorEDepth x ∧
      C.exteriorEDepth x ≤ intrinsicDiameter g C.carrier := by
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  have hfront : (frontier C.carrier).Nonempty := by
    by_contra h
    have hclopen : IsClopen C.carrier :=
      isClopen_iff_frontier_eq_empty.mpr (not_nonempty_iff_eq_empty.mp h)
    exact hproper (hclopen.connectedComponent_subset hx)
  obtain ⟨p, hp⟩ := hfront
  rw [C.carrier_open.frontier_eq] at hp
  have hbound : C.carrier ⊆ {y | g.edist x y ≤ intrinsicDiameter g C.carrier} := by
    intro y hy
    apply (g.m25_edist_le_intrinsicEDist C.carrier x y).trans
    exact le_sSup ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
  have hclosed : IsClosed {y | g.edist x y ≤ intrinsicDiameter g C.carrier} :=
    isClosed_le (continuous_const.edist continuous_id) continuous_const
  have hclosure := closure_minimal hbound hclosed
  change 0 < Metric.infEDist x C.carrierᶜ ∧
    Metric.infEDist x C.carrierᶜ ≤ intrinsicDiameter g C.carrier
  refine ⟨?_, (Metric.infEDist_le_edist_of_mem hp.2).trans (hclosure hp.1)⟩
  apply Metric.infEDist_pos_iff_notMem_closure.mpr
  rw [C.carrier_open.isClosed_compl.closure_eq]
  exact fun h => h hx

theorem ConnectedNeckCapCover.singleCap_of_component_subset
    (H : ConnectedNeckCapCover g) {x : M} (hx : x ∈ H.X)
    {C : CapCertificate g} (hC : C ∈ H.caps)
    (hK : connectedComponent x ⊆ C.carrier) :
    ∃ hX : H.X ⊆ C.carrier, NeckCapRegionCompatible g H (.singleCap C hX) := by
  refine ⟨(H.connected_X.subset_connectedComponent hx).trans hK, ?_⟩
  exact ⟨H.cap_epsilon C hC, H.cap_constant_bound C hC⟩

theorem ConnectedNeckCapCover.exists_core_cap_exteriorEDepth_near_max
    (H : ConnectedNeckCapCover g) {x : M}
    (hseed : ∃ C ∈ H.caps, x ∈ C.core)
    (hproper : ∀ C ∈ H.caps, x ∈ C.core → ¬ connectedComponent x ⊆ C.carrier)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C0 ∈ H.caps, x ∈ C0.core ∧
      (∀ C ∈ H.caps, x ∈ C.core →
        0 < C.exteriorEDepth x ∧ C.exteriorEDepth x < ⊤) ∧
      (∀ C ∈ H.caps, x ∈ C.core →
        (C.exteriorEDepth x).toReal < (C0.exteriorEDepth x).toReal + δ) := by
  classical
  obtain ⟨seed, hseed, hxseed⟩ := hseed
  let B : ℝ := H.cap_constant * (seed.connection.scalarCurvature x) ^ (-1 / 2 : ℝ)
  have hbounds : ∀ C ∈ H.caps, x ∈ C.core →
      0 < C.exteriorEDepth x ∧ C.exteriorEDepth x < ENNReal.ofReal B := by
    intro C hC hxC
    have hxcarrier := C.m25_core_subset_carrier hxC
    have hd := C.exteriorEDepth_pos_le_intrinsicDiameter hxcarrier (hproper C hC hxC)
    have hdiam := C.intrinsicDiameter_lt_of_mem hxcarrier (H.cap_constant_bound C hC)
    rw [scalarCurvature_eq_of_metric C.connection seed.connection x] at hdiam
    exact ⟨hd.1, hd.2.trans_lt hdiam⟩
  let F := {C : CapCertificate g // C ∈ H.caps ∧ x ∈ C.core}
  let n : F → ℕ := fun C => ⌊(C.val.exteriorEDepth x).toReal / δ⌋₊
  have hnonempty : (range n).Nonempty :=
    ⟨n ⟨seed, hseed, hxseed⟩, mem_range_self _⟩
  have hbounded : BddAbove (range n) := by
    refine ⟨⌊B / δ⌋₊, ?_⟩
    rintro k ⟨C, rfl⟩
    apply Nat.floor_mono
    exact div_le_div_of_nonneg_right
      (ENNReal.toReal_lt_of_lt_ofReal (hbounds C.val C.property.1 C.property.2).2).le hδ.le
  obtain ⟨C0, hC0⟩ := Nat.sSup_mem hnonempty hbounded
  refine ⟨C0.val, C0.property.1, C0.property.2, ?_, ?_⟩
  · intro C hC hxC
    have h := hbounds C hC hxC
    exact ⟨h.1, h.2.trans_le le_top⟩
  · intro C hC hxC
    have hmax : n ⟨C, hC, hxC⟩ ≤ n C0 := by
      rw [hC0]
      exact le_csSup hbounded (mem_range_self _)
    have hmaxR : (n ⟨C, hC, hxC⟩ : ℝ) ≤ (n C0 : ℝ) := by exact_mod_cast hmax
    have hfloorlt := Nat.lt_floor_add_one ((C.exteriorEDepth x).toReal / δ)
    have hfloorle : (⌊(C0.val.exteriorEDepth x).toReal / δ⌋₊ : ℝ) ≤
        (C0.val.exteriorEDepth x).toReal / δ :=
      Nat.floor_le (div_nonneg ENNReal.toReal_nonneg hδ.le)
    have hquot : (C.exteriorEDepth x).toReal / δ <
        (C0.val.exteriorEDepth x).toReal / δ + 1 := by
      dsimp only [n] at hmaxR
      linarith
    apply (div_lt_div_iff_of_pos_right hδ).mp
    simpa only [add_div, div_self hδ.ne'] using hquot

theorem ConnectedNeckCapCover.singleCap_or_exists_core_cap_exteriorEDepth_near_max
    (H : ConnectedNeckCapCover g) {x : M} (hx : x ∈ H.X)
    (hseed : ∃ C ∈ H.caps, x ∈ C.core) {δ : ℝ} (hδ : 0 < δ) :
    (∃ C ∈ H.caps, ∃ hX : H.X ⊆ C.carrier,
      NeckCapRegionCompatible g H (.singleCap C hX)) ∨
      ∃ C0 ∈ H.caps, x ∈ C0.core ∧
        (∀ C ∈ H.caps, x ∈ C.core →
          0 < C.exteriorEDepth x ∧ C.exteriorEDepth x < ⊤) ∧
        (∀ C ∈ H.caps, x ∈ C.core →
          (C.exteriorEDepth x).toReal < (C0.exteriorEDepth x).toReal + δ) := by
  classical
  by_cases hcap : ∃ C ∈ H.caps, H.X ⊆ C.carrier
  · obtain ⟨C, hC, hX⟩ := hcap
    exact Or.inl ⟨C, hC, hX, H.cap_epsilon C hC, H.cap_constant_bound C hC⟩
  · apply Or.inr
    apply H.exists_core_cap_exteriorEDepth_near_max hseed ?_ hδ
    intro C hC _ hK
    exact hcap ⟨C, hC, (H.connected_X.subset_connectedComponent hx).trans hK⟩

end PoincareConjecture
