import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.TubeRegion
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cylinder.Tails
import Mathlib.Topology.Order.IntermediateValue









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

namespace OpenCylinderModel

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {U : Set M}

theorem isCompact_axial_sphere (Q : OpenCylinderModel U)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    IsCompact (Q.coordinate '' (univ ×ˢ ({a} : Set ℝ))) := by
  simpa only [Icc_self] using Q.isCompact_coordinate_slab ha.1 ha.2


theorem exists_side_of_connected (Q : OpenCylinderModel U) {S : Set M}
    (hS : IsConnected S) (hSU : S ⊆ U) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (havoid : Disjoint S (Q.coordinate '' (univ ×ˢ ({a} : Set ℝ)))) :
    ∃ side : Bool, S ⊆ Q.tail side a := by
  have hne : ∀ x ∈ S, (Q.inverse x).2 ≠ a := by
    intro x hx heq
    apply Set.disjoint_left.mp havoid hx
    exact ⟨Q.inverse x, ⟨mem_univ _, heq⟩, Q.right_inverse (hSU hx)⟩
  have hf : ContinuousOn (fun x => (Q.inverse x).2) S :=
    (Q.inverse_smooth.continuousOn.mono hSU).snd
  obtain ⟨x, hx⟩ := hS.nonempty
  rcases lt_or_gt_of_ne (hne x hx) with hxa | hax
  · refine ⟨false, fun y hy => (Q.mem_tail_iff false ha).mpr ⟨hSU hy, ?_⟩⟩
    change (Q.inverse y).2 < a
    by_contra h
    obtain ⟨z, hz, hza⟩ := hS.isPreconnected.intermediate_value hx hy hf
      ⟨hxa.le, le_of_not_gt h⟩
    exact hne z hz hza
  · refine ⟨true, fun y hy => (Q.mem_tail_iff true ha).mpr ⟨hSU hy, ?_⟩⟩
    change a < (Q.inverse y).2
    by_contra h
    obtain ⟨z, hz, hza⟩ := hS.isPreconnected.intermediate_value hy hx hf
      ⟨le_of_not_gt h, hax.le⟩
    exact hne z hz hza

end OpenCylinderModel

namespace TerminalEnd

variable {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {E : GeneralizedFlowExtension F T} {K : TerminalComponentPath E}



theorem exists_tube_direction (e : TerminalEnd K) (n : ℕ)
    (tube : EpsilonTubeCertificate (E.extended.metric T) (Subtype.val '' e.tail n)) :
    ∃ side : Bool, ∀ a ∈ Ioo (0 : ℝ) 1, ∃ k : ℕ, n ≤ k ∧
      ∀ m : ℕ, k ≤ m → Subtype.val '' e.tail m ⊆ tube.cylinder.tail side a := by
  let Q := tube.cylinder
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  obtain ⟨k₀, hk₀⟩ := e.exists_tail_disjoint_compact (Q.isCompact_axial_sphere hhalf)
  let k := max n k₀
  have hU : Subtype.val '' e.tail k ⊆ tube.carrier :=
    (Set.image_mono (e.nested (le_max_left n k₀))).trans tube.contains_X
  obtain ⟨side, hside⟩ := Q.exists_side_of_connected (e.tail_image_connected k) hU
    hhalf (hk₀ k (le_max_right n k₀))
  refine ⟨side, fun a ha => ?_⟩
  obtain ⟨l, hl⟩ := e.exists_tail_disjoint_compact
    (Q.isCompact_coordinate_slab (lt_min ha.1 hhalf.1) (max_lt ha.2 hhalf.2))
  refine ⟨max k l, (le_max_left n k₀).trans (le_max_left k l), fun m hm x hx => ?_⟩
  have hmk : k ≤ m := (le_max_left k l).trans hm
  have hml : l ≤ m := (le_max_right k l).trans hm
  have hxk : x ∈ Subtype.val '' e.tail k := Set.image_mono (e.nested hmk) hx
  have hxU := hU hxk
  have hinit := ((Q.mem_tail_iff side hhalf).mp (hside hxk)).2
  apply (Q.mem_tail_iff side ha).mpr
  refine ⟨hxU, ?_⟩
  have havoid := Set.disjoint_left.mp (hl m hml) hx
  cases side
  · change (Q.inverse x).2 < a
    change (Q.inverse x).2 < 1 / 2 at hinit
    by_contra h
    apply havoid
    exact ⟨Q.inverse x, ⟨mem_univ _,
      (min_le_left a (1 / 2)).trans (le_of_not_gt h),
      hinit.le.trans (le_max_right a (1 / 2))⟩, Q.right_inverse hxU⟩
  · change a < (Q.inverse x).2
    change 1 / 2 < (Q.inverse x).2 at hinit
    by_contra h
    apply havoid
    exact ⟨Q.inverse x, ⟨mem_univ _,
      (min_le_right a (1 / 2)).trans hinit.le,
      (le_of_not_gt h).trans (le_max_left a (1 / 2))⟩, Q.right_inverse hxU⟩

end TerminalEnd

end PoincareConjecture
