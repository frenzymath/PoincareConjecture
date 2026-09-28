import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.CapCompactness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Geometry.EndCut.Topology.Escaping

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.TerminalEnd

variable {G : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {E : GeneralizedFlowExtension G T} {K : TerminalComponentPath E} (e : TerminalEnd K)

theorem exists_tail_subset_coordinateTail {epsilon : ℝ}
    (horn : StrongHorn E epsilon) (n : ℕ)
    (htail : Subtype.val '' e.tail n ⊆ horn.carrier)
    (b : ℝ) (hb : b < 1) :
    ∃ m, n ≤ m ∧ Subtype.val '' e.tail m ⊆ horn.coordinateTail b := by
  obtain ⟨k, hk⟩ := e.exists_tail_disjoint_compact (horn.isCompact_coordinatePrefix hb)
  refine ⟨max n k, le_max_left _ _, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  have hyn : y ∈ e.tail n := e.nested (le_max_left _ _) hy
  exact (horn.carrier_subset_prefix_union_tail b (htail ⟨y, hyn, rfl⟩)).resolve_left
    (fun h => disjoint_left.mp (hk _ (le_max_right _ _)) ⟨y, hy, rfl⟩ h)

theorem exists_tail_subset_hornEndCut {epsilon delta rho : ℝ}
    {horn : StrongHorn E epsilon} {N : TerminalStrongNeck E delta}
    (cut : HornEndCut horn N rho) (n : ℕ)
    (htail : Subtype.val '' e.tail n ⊆ horn.carrier) :
    ∃ m, n ≤ m ∧ Subtype.val '' e.tail m ⊆ cut.carrier := by
  obtain ⟨m, hnm, hm⟩ := e.exists_tail_subset_coordinateTail horn n htail
    cut.tail_level cut.tail_level_lt_one
  exact ⟨m, hnm, hm.trans cut.contains_tail⟩

theorem exists_coordinateTail_subset {epsilon : ℝ}
    (horn : StrongHorn E epsilon) (hcomponent : horn.carrier ⊆ K.component)
    (n₀ : ℕ) (htail : Subtype.val '' e.tail n₀ ⊆ horn.carrier) (n : ℕ) :
    ∃ b : ℝ, 0 ≤ b ∧ b < 1 ∧ horn.coordinateTail b ⊆ Subtype.val '' e.tail n := by
  let L : Set (E.extended.slice T).carrier := Subtype.val '' e.exhaustion n
  have hL : IsCompact L := (e.exhaustion.isCompact n).image continuous_subtype_val
  obtain ⟨b, hb0, hb1, havoid⟩ := horn.exists_tail_avoiding_compact L hL
  have hdis : Disjoint (horn.coordinateTail b) L := by
    apply disjoint_left.mpr
    rintro y ⟨⟨s, t⟩, ⟨_, ht, ht1⟩, rfl⟩ hy
    exact havoid s t ht ht1 hy
  have hsub : horn.coordinateTail b ⊆ K.component :=
    (horn.coordinateTail_subset_carrier hb0).trans hcomponent
  have hconn : IsPreconnected
      (Subtype.val ⁻¹' horn.coordinateTail b : Set K.component) := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr hsub]
    exact horn.isPreconnected_coordinateTail hb0
  have hout : (Subtype.val ⁻¹' horn.coordinateTail b : Set K.component) ⊆
      (e.exhaustion n)ᶜ := by
    intro x hx hxL
    exact disjoint_left.mp hdis hx ⟨x, hxL, rfl⟩
  obtain ⟨m, _, hm⟩ := e.exists_tail_subset_coordinateTail horn n₀ htail b hb1
  obtain ⟨x, hx⟩ := (e.tail_connected (max m n)).nonempty
  have hxm : x ∈ e.tail m := e.nested (le_max_left _ _) hx
  have hxn : x ∈ e.tail n := e.nested (le_max_right _ _) hx
  have hxV : x ∈ (Subtype.val ⁻¹' horn.coordinateTail b : Set K.component) :=
    hm ⟨x, hxm, rfl⟩
  have heq : connectedComponentIn (e.exhaustion n)ᶜ x = e.tail n := by
    obtain ⟨z, _, htailn⟩ := e.tail_component n
    rw [htailn] at hxn ⊢
    exact (connectedComponentIn_eq hxn).symm
  have hcontained := hconn.subset_connectedComponentIn hxV hout
  rw [heq] at hcontained
  exact ⟨b, hb0, hb1, fun y hy => ⟨⟨y, hsub hy⟩, hcontained hy, rfl⟩⟩

end PoincareConjecture.TerminalEnd

namespace PoincareConjecture.HornEndCut

variable {G : GeneralizedRicciFlowData.{u}} {T epsilon delta rho : ℝ}
  {E : GeneralizedFlowExtension G T} {horn : StrongHorn E epsilon}
  {N : TerminalStrongNeck E delta}

theorem carrier_eq_escapingComponent (cut : HornEndCut horn N rho) :
    cut.carrier = horn.escapingComponent N.central_sphere N.isCompact_central_sphere := by
  rw [cut.component_eq]
  apply horn.escapingComponent_eq_of_not_subset_compact
  intro L hL hsub
  exact cut.escapes_compact L hL (cut.component_eq ▸ hsub)

end PoincareConjecture.HornEndCut
