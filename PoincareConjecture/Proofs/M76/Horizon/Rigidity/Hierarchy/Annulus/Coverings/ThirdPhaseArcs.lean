import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.CoordinateHomotopy









set_option autoImplicit false
open Set

namespace IsCoveringMap

theorem exists_finite_vertical_arc_family
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [CompactSpace X] [T2Space Y]
    {c : C(X, unitInterval × Y)} (hc : IsCoveringMap c) (theta : Y) :
    ∃ (n : ℕ) (arc : Fin n → C(unitInterval, X)),
      (∀ i, Topology.IsEmbedding (arc i)) ∧
      Pairwise (fun i j => Disjoint (range (arc i)) (range (arc j))) ∧
      (⋃ i, range (arc i)) = {x | (c x).2 = theta} ∧
      (∀ i t, c (arc i t) = (t, theta)) ∧
      ∀ i t, (c (arc i t)).1 = 0 ∨ (c (arc i t)).1 = 1 ↔ t = 0 ∨ t = 1 := by
  classical
  let B : Set X := c ⁻¹' {(0, theta)}
  have hB : IsCompact B := (isClosed_singleton.preimage c.continuous).isCompact
  let : CompactSpace B := isCompact_iff_compactSpace.mp hB
  let : DiscreteTopology B := (hc (0, theta)).discreteTopology_fiber
  let : Finite B := finite_of_compact_of_discrete
  let : Fintype B := Fintype.ofFinite B
  let : ContractibleSpace unitInterval :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
  let : LocallyPathConnectedSpace unitInterval :=
    (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  let base : C(unitInterval, unitInterval × Y) :=
    ⟨fun t => (t, theta), continuous_id.prodMk continuous_const⟩
  have hex (x : B) := hc.existsUnique_continuousMap_lifts base 0 x x.property
  choose lift hlift hunique using hex
  have hcoord (x : B) (t : unitInterval) : c (lift x t) = (t, theta) :=
    congr_fun (hlift x).2 t
  have hembed (x : B) : Topology.IsEmbedding (lift x) := by
    apply (lift x).continuous.isClosedEmbedding ?_ |>.isEmbedding
    intro s t hst
    have h := congrArg (fun z : X => (c z).1) hst
    simpa only [hcoord] using h
  have hdis : Pairwise (fun x y : B => Disjoint (range (lift x)) (range (lift y))) := by
    intro x y hxy
    apply disjoint_left.mpr
    rintro z ⟨s, rfl⟩ ⟨t, hst⟩
    have hts : t = s := by
      have h := congrArg (fun z : X => (c z).1) hst
      simpa only [hcoord] using h
    subst t
    have heq := hc.eq_of_comp_eq (lift y).continuous (lift x).continuous
      ((hlift y).2.trans (hlift x).2.symm) s hst
    apply hxy
    apply Subtype.ext
    exact ((hlift x).1).symm.trans ((congr_fun heq 0).symm.trans (hlift y).1)
  have hwhole : (⋃ x : B, range (lift x)) = {x | (c x).2 = theta} := by
    ext x
    constructor
    · intro hx
      obtain ⟨z, t, rfl⟩ := mem_iUnion.mp hx
      exact congrArg Prod.snd (hcoord z t)
    · intro hx
      obtain ⟨L, hL, _⟩ := hc.existsUnique_continuousMap_lifts base (c x).1 x
        (Prod.ext rfl hx)
      have hzero : L 0 ∈ B := congr_fun hL.2 0
      let z : B := ⟨L 0, hzero⟩
      have heq : L = lift z := hunique z L ⟨rfl, hL.2⟩
      exact mem_iUnion.mpr ⟨z, (c x).1, by rw [← heq]; exact hL.1⟩
  let e := Fintype.equivFin B
  refine ⟨Fintype.card B, fun i => lift (e.symm i),
    fun i => hembed _, fun i j hij => hdis (fun h => hij (e.symm.injective h)), ?_,
    fun i t => hcoord _ t, ?_⟩
  · rw [← hwhole]
    apply le_antisymm
    · exact iUnion_mono' (fun i => ⟨e.symm i, subset_rfl⟩)
    · intro x hx
      obtain ⟨z, hz⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨e z, by simpa only [e.symm_apply_apply] using hz⟩
  · intro i t
    rw [hcoord]

end IsCoveringMap

namespace PoincareConjecture.M76

open Geometry PLAnnularStrip

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "Ann" => squareAnnulus 8 1
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem exists_hamiltonZero_annulus_third_phase_arc_family
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    (chi : C(H0, H0)) {j : ℝ × ℝ → X0}
    (hj : PolyhedralPLInCharts e j Ann)
    (hji : Topology.IsEmbedding (fun z : Ann => j z))
    (c : C(Ann, unitInterval × C0)) (hc : IsCoveringMap c)
    (delta0 delta1 : ℝ) (theta xi : C0)
    (hformula : ∀ z : Ann, hamiltonZeroAmbientMap chi (j z) =
      hamiltonZeroAnnulusTargetMap delta0 delta1 theta (c z)) :
    ∃ (n : ℕ) (arc : Fin n → C(unitInterval, X0)),
      (∀ i, Topology.IsEmbedding (arc i)) ∧
      Pairwise (fun i k => Disjoint (range (arc i)) (range (arc k))) ∧
      (⋃ i, range (arc i)) =
        j '' Ann ∩ {x | (Q0 (hamiltonZeroAmbientMap chi x)).1.1 = xi} ∧
      ∀ i t, hamiltonZeroAmbientMap chi (arc i t) =
        hamiltonZeroAnnulusTargetMap delta0 delta1 theta (t, xi) := by
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  let : CompactSpace Ann := Dehn.annulusCylinderHomeomorph.compactSpace
  obtain ⟨n, arc, hembed, hdis, hwhole, hcoord, _⟩ :=
    hc.exists_finite_vertical_arc_family xi
  let J : C(Ann, X0) := ⟨fun z => j z, hj.continuousOn.domRestrict⟩
  have hphase (z : Ann) : (Q0 (hamiltonZeroAmbientMap chi (j z))).1.1 = (c z).2 := by
    rw [hformula, hamiltonZeroAnnulusTargetMap_coordinates]
  refine ⟨n, fun i => J.comp (arc i), fun i => hji.comp (hembed i), ?_, ?_, ?_⟩
  · intro i k hik
    apply disjoint_left.mpr
    rintro x ⟨s, rfl⟩ ⟨t, heq⟩
    have hst : arc k t = arc i s := hji.injective heq
    exact disjoint_left.mp (hdis hik) ⟨s, rfl⟩ ⟨t, hst⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨i, t, rfl⟩ := mem_iUnion.mp hx
      refine ⟨⟨arc i t, (arc i t).property, rfl⟩, ?_⟩
      change (Q0 (hamiltonZeroAmbientMap chi (j (arc i t)))).1.1 = xi
      rw [hphase, hcoord]
    · rintro ⟨⟨z, hz, rfl⟩, hxi⟩
      have hzphase : (c ⟨z, hz⟩).2 = xi := (hphase ⟨z, hz⟩).symm.trans hxi
      have hzwhole : (⟨z, hz⟩ : Ann) ∈ ⋃ i, range (arc i) := hwhole.symm.subset hzphase
      obtain ⟨i, t, ht⟩ := mem_iUnion.mp hzwhole
      exact mem_iUnion.mpr ⟨i, t, congrArg J ht⟩
  · intro i t
    change hamiltonZeroAmbientMap chi (j (arc i t)) = _
    rw [hformula, hcoord]

end PoincareConjecture.M76
