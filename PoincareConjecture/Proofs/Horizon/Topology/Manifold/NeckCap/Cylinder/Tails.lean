import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Models
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.OpenCylinderModel

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M} (T : OpenCylinderModel U)

theorem coordinate_mem {z : RoundCylinderSpace} (hz : z ∈ univ ×ˢ Ioo (0 : ℝ) 1) :
    T.coordinate z ∈ U := by
  have h := (T.homeomorph (z.1, ⟨z.2, hz.2⟩)).property
  rwa [T.coordinate_eq] at h

theorem mem_tail_iff (side : Bool) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) {x : M} :
    x ∈ T.tail side a ↔ x ∈ U ∧
      if side then a < (T.inverse x).2 else (T.inverse x).2 < a := by
  cases side
  · change x ∈ T.coordinate '' (univ ×ˢ Ioo 0 a) ↔ x ∈ U ∧ (T.inverse x).2 < a
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hdom : z ∈ univ ×ˢ Ioo (0 : ℝ) 1 :=
        ⟨mem_univ _, hz.2.1, hz.2.2.trans ha.2⟩
      refine ⟨T.coordinate_mem hdom, ?_⟩
      rw [T.left_inverse hdom]
      exact hz.2.2
    · rintro ⟨hx, hlt⟩
      exact ⟨T.inverse x, ⟨mem_univ _, (T.inverse_mem x hx).2.1, hlt⟩,
        T.right_inverse hx⟩
  · change x ∈ T.coordinate '' (univ ×ˢ Ioo a 1) ↔ x ∈ U ∧ a < (T.inverse x).2
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hdom : z ∈ univ ×ˢ Ioo (0 : ℝ) 1 :=
        ⟨mem_univ _, ha.1.trans hz.2.1, hz.2.2⟩
      refine ⟨T.coordinate_mem hdom, ?_⟩
      rw [T.left_inverse hdom]
      exact hz.2.1
    · rintro ⟨hx, hlt⟩
      exact ⟨T.inverse x, ⟨mem_univ _, hlt, (T.inverse_mem x hx).2.2⟩,
        T.right_inverse hx⟩

theorem tail_subset (side : Bool) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    T.tail side a ⊆ U := fun _ hx => ((T.mem_tail_iff side ha).mp hx).1

private instance : ConnectedSpace UnitTwoSphere := by
  apply isConnected_iff_connectedSpace.mp
  exact isConnected_sphere
    (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)

include T in

theorem isConnected_carrier : IsConnected U := by
  have heq : T.coordinate '' (univ ×ˢ Ioo (0 : ℝ) 1) = U := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact T.coordinate_mem hz
    · intro x hx
      exact ⟨T.inverse x, T.inverse_mem x hx, T.right_inverse hx⟩
  rw [← heq]
  exact (isConnected_univ.prod (isConnected_Ioo (by norm_num : (0 : ℝ) < 1))).image
    T.coordinate T.coordinate_smooth.continuousOn

theorem isConnected_tail (side : Bool) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    IsConnected (T.tail side a) := by
  cases side
  · apply (isConnected_univ.prod (isConnected_Ioo ha.1)).image
    apply T.coordinate_smooth.continuousOn.mono
    exact fun _ hz => ⟨mem_univ _, hz.2.1, hz.2.2.trans ha.2⟩
  · apply (isConnected_univ.prod (isConnected_Ioo ha.2)).image
    apply T.coordinate_smooth.continuousOn.mono
    exact fun _ hz => ⟨mem_univ _, ha.1.trans hz.2.1, hz.2.2⟩

theorem coordinate_slab_subset {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    T.coordinate '' (univ ×ˢ Icc a b) ⊆ U := by
  rintro _ ⟨z, hz, rfl⟩
  exact T.coordinate_mem ⟨mem_univ _, ha.trans_le hz.2.1, hz.2.2.trans_lt hb⟩

theorem isCompact_coordinate_slab {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    IsCompact (T.coordinate '' (univ ×ˢ Icc a b)) := by
  apply (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
  apply T.coordinate_smooth.continuousOn.mono
  exact fun _ hz => ⟨mem_univ _, ha.trans_le hz.2.1, hz.2.2.trans_lt hb⟩

theorem diff_tails_subset_coordinate_slab {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) (1 / 2)) :
    U \ (T.tail false a ∪ T.tail true (1 - a)) ⊆
      T.coordinate '' (univ ×ˢ Icc a (1 - a)) := by
  have haone : a ∈ Ioo (0 : ℝ) 1 := ⟨ha.1, by linarith [ha.2]⟩
  have hcomplement : 1 - a ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [ha.1, ha.2]
  rintro x ⟨hx, hout⟩
  refine ⟨T.inverse x, ⟨mem_univ _, ?_, ?_⟩, T.right_inverse hx⟩
  · by_contra h
    exact hout (Or.inl ((T.mem_tail_iff false haone).mpr ⟨hx, lt_of_not_ge h⟩))
  · by_contra h
    exact hout (Or.inr ((T.mem_tail_iff true hcomplement).mpr ⟨hx, lt_of_not_ge h⟩))

theorem exists_tails_disjoint_of_isCompact {K : Set M} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ a ∈ Ioo (0 : ℝ) (1 / 2),
      Disjoint (T.tail false a) K ∧ Disjoint (T.tail true (1 - a)) K ∧
      IsCompact (T.coordinate '' (univ ×ˢ Icc a (1 - a))) ∧
      U \ (T.tail false a ∪ T.tail true (1 - a)) ⊆
        T.coordinate '' (univ ×ˢ Icc a (1 - a)) := by
  have hcont : ContinuousOn (fun x => (T.inverse x).2) K :=
    T.inverse_smooth.continuousOn.snd.mono hKU
  obtain ⟨l, hl, hlower⟩ := hK.exists_forall_le' hcont
    (fun x hx => (T.inverse_mem x (hKU hx)).2.1)
  obtain ⟨r, hr, hupper⟩ := hK.exists_forall_le' (continuousOn_const.sub hcont)
    (fun x hx => sub_pos.mpr (T.inverse_mem x (hKU hx)).2.2)
  obtain ⟨a, ha, ham⟩ := exists_between
    (lt_min (lt_min hl hr) (by norm_num : (0 : ℝ) < 1 / 2))
  have hal : a < l := ham.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have har : a < r := ham.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hahalf : a < 1 / 2 := ham.trans_le (min_le_right _ _)
  have haone : a ∈ Ioo (0 : ℝ) 1 := ⟨ha, by linarith⟩
  have hcomplement : 1 - a ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith
  refine ⟨a, ⟨ha, hahalf⟩, ?_, ?_, T.isCompact_coordinate_slab ha hcomplement.2,
    T.diff_tails_subset_coordinate_slab ⟨ha, hahalf⟩⟩
  · rw [disjoint_left]
    intro x hxtail hxK
    have hlt := ((T.mem_tail_iff false haone).mp hxtail).2
    have hle := hlower x hxK
    change (T.inverse x).2 < a at hlt
    linarith
  · rw [disjoint_left]
    intro x hxtail hxK
    have hlt := ((T.mem_tail_iff true hcomplement).mp hxtail).2
    have hle := hupper x hxK
    change r ≤ 1 - (T.inverse x).2 at hle
    change 1 - a < (T.inverse x).2 at hlt
    linarith

end PoincareConjecture.OpenCylinderModel
