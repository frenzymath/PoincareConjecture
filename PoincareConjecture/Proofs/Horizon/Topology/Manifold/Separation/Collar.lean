import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

open Set Topology

namespace Poincare.Topology

variable {Y X : Type*} [TopologicalSpace Y] [ConnectedSpace Y]
  [TopologicalSpace X] {r : ℝ} (hr : 0 < r) {U : Set X}
  (e : (Y × Ioo (-r) r) ≃ₜ U)

include hr

theorem isConnected_collar_negative :
    IsConnected ((fun z => (e z : X)) '' {z | (z.2 : ℝ) < 0}) := by
  have hc : IsConnected {t : Ioo (-r) r | (t : ℝ) < 0} := by
    have h := (isConnected_Ioo (neg_lt_zero.mpr hr)).preimage_of_isOpenMap
      (f := (Subtype.val : Ioo (-r) r → ℝ)) Subtype.val_injective
      isOpen_Ioo.isOpenMap_subtype_val (by
        intro t ht
        exact ⟨⟨t, ht.1, ht.2.trans hr⟩, rfl⟩)
    convert h using 1
    ext t
    exact (and_iff_right t.property.1).symm
  have hset : {z : Y × Ioo (-r) r | (z.2 : ℝ) < 0} =
      univ ×ˢ {t : Ioo (-r) r | (t : ℝ) < 0} := by ext z; simp
  rw [hset]
  exact (isConnected_univ.prod hc).image _
    (continuous_subtype_val.comp e.continuous).continuousOn

theorem isConnected_collar_positive :
    IsConnected ((fun z => (e z : X)) '' {z | 0 < (z.2 : ℝ)}) := by
  have hc : IsConnected {t : Ioo (-r) r | 0 < (t : ℝ)} := by
    have h := (isConnected_Ioo hr).preimage_of_isOpenMap
      (f := (Subtype.val : Ioo (-r) r → ℝ)) Subtype.val_injective
      isOpen_Ioo.isOpenMap_subtype_val (by
        intro t ht
        exact ⟨⟨t, (neg_lt_zero.mpr hr).trans ht.1, ht.2⟩, rfl⟩)
    convert h using 1
    ext t
    exact (and_iff_left t.property.2).symm
  have hset : {z : Y × Ioo (-r) r | 0 < (z.2 : ℝ)} =
      univ ×ˢ {t : Ioo (-r) r | 0 < (t : ℝ)} := by ext z; simp
  rw [hset]
  exact (isConnected_univ.prod hc).image _
    (continuous_subtype_val.comp e.continuous).continuousOn

omit [ConnectedSpace Y] in

theorem collar_center_mem_closure_negative (y : Y) :
    (e (y, ⟨0, by constructor <;> linarith⟩) : X) ∈
      closure ((fun z => (e z : X)) '' {z | (z.2 : ℝ) < 0}) := by
  apply mem_closure_image (continuous_subtype_val.comp e.continuous).continuousAt
  have hset : {z : Y × Ioo (-r) r | (z.2 : ℝ) < 0} =
      univ ×ˢ {t : Ioo (-r) r | (t : ℝ) < 0} := by ext z; simp
  rw [hset]
  rw [closure_prod_eq, closure_univ]
  refine ⟨mem_univ _, ?_⟩
  apply IsOpenMap.preimage_closure_subset_closure_preimage
    (isOpen_Ioo : IsOpen (Ioo (-r) r)).isOpenMap_subtype_val (s := Iio (0 : ℝ))
  change (0 : ℝ) ∈ closure (Iio 0)
  rw [closure_Iio]
  exact (le_rfl : (0 : ℝ) ≤ 0)

omit [ConnectedSpace Y] in

theorem collar_center_mem_closure_positive (y : Y) :
    (e (y, ⟨0, by constructor <;> linarith⟩) : X) ∈
      closure ((fun z => (e z : X)) '' {z | 0 < (z.2 : ℝ)}) := by
  apply mem_closure_image (continuous_subtype_val.comp e.continuous).continuousAt
  have hset : {z : Y × Ioo (-r) r | 0 < (z.2 : ℝ)} =
      univ ×ˢ {t : Ioo (-r) r | 0 < (t : ℝ)} := by ext z; simp
  rw [hset]
  rw [closure_prod_eq, closure_univ]
  refine ⟨mem_univ _, ?_⟩
  apply IsOpenMap.preimage_closure_subset_closure_preimage
    (isOpen_Ioo : IsOpen (Ioo (-r) r)).isOpenMap_subtype_val (s := Ioi (0 : ℝ))
  change (0 : ℝ) ∈ closure (Ioi 0)
  rw [closure_Ioi]
  exact (le_rfl : (0 : ℝ) ≤ 0)

end Poincare.Topology
