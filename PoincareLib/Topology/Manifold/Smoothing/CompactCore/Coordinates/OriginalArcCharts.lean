import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Coordinates.FinalEndpointArcPairChart
import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Coordinates.InteriorArcPairChart

/-!
# Actual charts for whole-star refinement around the protected arc

Off the complete arc, the chosen chart misses its entire image.
On it, the actual endpoint ray or interior line chart lies in the
prescribed open region. The endpoint chart also lies in its own
prescribed neighborhood, retaining the whole old-domain and frontier
equations. See Wall013, section 3, and the checked Wall011 pair charts.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

/-- Every original point has an actual compatible chart suitable
for simultaneous star refinement. A chart meeting the arc has its
whole source in W and an exact line or negative-ray carrier equation.
The endpoint alternatives retain the entire old-domain halfspace
and full frontier in their prescribed endpoint neighborhoods.
See013, section 3; no star-containment or tube supplier is used. -/
theorem PLDomain.exists_original_arc_model_chart
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {L : Set X} (he : PLDomain e L)
    {q : ℝ → X} (hq : PolyhedralPLInCharts e q I) (hqi : InjOn q I)
    (hzero : q 0 ∈ frontier L) (hone : q 1 ∈ frontier L)
    (hproper : ∀ t ∈ Ioo (0 : ℝ) 1, q t ∉ L)
    {W : Set X} (hW : IsOpen W) (hqW : MapsTo q I W)
    (U : Fin 2 → Set X) (hU : ∀ i, IsOpen (U i))
    (hU0 : q 0 ∈ U 0) (hU1 : q 1 ∈ U 1) (x : X) :
    ∃ G : OpenPartialHomeomorph X V3,
      x ∈ G.source ∧ (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
      (G.source ⊆ (q '' I)ᶜ ∨
        (G.source ⊆ W ∧
          ((G.source ⊆ Lᶜ ∧ ∃ v : V3, v ≠ 0 ∧
            ∀ y ∈ G.source, y ∈ q '' I ↔ ∃ r : ℝ, G y = r • v) ∨
          ∃ (i : Fin 2) (A : V3 →L[ℝ] ℝ) (v : V3),
            G.source ⊆ U i ∧ A v = 1 ∧
            (∀ y ∈ G.source, y ∈ L ↔ 0 ≤ A (G y)) ∧
            (∀ y ∈ G.source, y ∈ frontier L ↔ A (G y) = 0) ∧
            ∀ y ∈ G.source,
              y ∈ q '' I ↔ ∃ r : ℝ, r ≤ 0 ∧ G y = r • v))) := by
  classical
  by_cases hxarc : x ∈ q '' I
  · obtain ⟨t, ht, rfl⟩ := hxarc
    by_cases ht0 : t = 0
    · subst t
      obtain ⟨G, A, v, hxG, hGW, _, hv, hGe, hhalf, hfront, harc⟩ :=
        he.exists_endpoint_arc_pair_chart hq hqi hzero hproper (hW.inter (hU 0))
          ⟨hqW ⟨le_rfl, zero_le_one⟩, hU0⟩
      exact ⟨G, hxG, hGe, Or.inr ⟨fun _ hy => (hGW hy).1,
        Or.inr ⟨0, A, v, fun _ hy => (hGW hy).2, hv, hhalf, hfront, harc⟩⟩⟩
    by_cases ht1 : t = 1
    · subst t
      obtain ⟨G, A, v, hxG, hGW, _, hv, hGe, hhalf, hfront, harc⟩ :=
        he.exists_final_endpoint_arc_pair_chart hq hqi hone hproper (hW.inter (hU 1))
          ⟨hqW ⟨zero_le_one, le_rfl⟩, hU1⟩
      exact ⟨G, hxG, hGe, Or.inr ⟨fun _ hy => (hGW hy).1,
        Or.inr ⟨1, A, v, fun _ hy => (hGW hy).2, hv, hhalf, hfront, harc⟩⟩⟩
    have hti : t ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
    obtain ⟨G, v, hv, hxG, hGW, _, hGe, harc⟩ :=
      OpenPartialHomeomorph.exists_interior_arc_pair_chart e he.cover he.compatible
        hq hqi hti (hW.sdiff he.closed) ⟨hqW ht, hproper t hti⟩
    exact ⟨G, hxG, hGe, Or.inr ⟨fun _ hy => (hGW hy).1,
      Or.inl ⟨fun _ hy => (hGW hy).2, v, hv, harc⟩⟩⟩
  · have hclosed : IsClosed (q '' I) :=
      (isCompact_Icc.image_of_continuousOn hq.continuousOn).isClosed
    obtain ⟨i, hxi⟩ := he.cover x
    let G := (e i).restrOpen (q '' I)ᶜ hclosed.isOpen_compl
    refine ⟨G, ⟨hxi, hxarc⟩, ?_, Or.inl (fun _ hy => hy.2)⟩
    intro j
    exact (e j).piecewiseAffine_compatible_restrOpen_right (e i)
      (he.compatible j i) hclosed.isOpen_compl

end PoincareMT.M76
