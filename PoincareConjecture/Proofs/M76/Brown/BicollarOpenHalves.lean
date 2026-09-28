import PoincareConjecture.Proofs.M76.Brown.BicollarHeightSign
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.DenselyOrdered

set_option autoImplicit false

open Set

namespace BrownCollar

variable {X : Type*} [TopologicalSpace X] {S C : Set X}

def positiveBicollarMap (H : (S × Ioo (-1 : ℝ) 1) ≃ₜ C)
    (z : S × Ioo (0 : ℝ) 1) : X :=
  H (z.1, ⟨z.2.val, lt_trans (by norm_num) z.2.property.1, z.2.property.2⟩)

def negativeBicollarMap (H : (S × Ioo (-1 : ℝ) 1) ≃ₜ C)
    (z : S × Ioo (-1 : ℝ) 0) : X :=
  H (z.1, ⟨z.2.val, z.2.property.1, lt_trans z.2.property.2 (by norm_num)⟩)

theorem continuous_positiveBicollarMap (H : (S × Ioo (-1 : ℝ) 1) ≃ₜ C) :
    Continuous (positiveBicollarMap H) :=
  continuous_subtype_val.comp (H.continuous.comp
    (continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)))

theorem continuous_negativeBicollarMap (H : (S × Ioo (-1 : ℝ) 1) ≃ₜ C) :
    Continuous (negativeBicollarMap H) :=
  continuous_subtype_val.comp (H.continuous.comp
    (continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)))

theorem mem_range_positiveBicollarMap (H : (S × Ioo (-1 : ℝ) 1) ≃ₜ C)
    (z : S × Ioo (-1 : ℝ) 1) (hz : 0 < (z.2 : ℝ)) :
    (H z : X) ∈ range (positiveBicollarMap H) := by
  exact ⟨(z.1, ⟨z.2.val, hz, z.2.property.2⟩), rfl⟩

theorem mem_range_negativeBicollarMap (H : (S × Ioo (-1 : ℝ) 1) ≃ₜ C)
    (z : S × Ioo (-1 : ℝ) 1) (hz : (z.2 : ℝ) < 0) :
    (H z : X) ∈ range (negativeBicollarMap H) := by
  exact ⟨(z.1, ⟨z.2.val, z.2.property.1, hz⟩), rfl⟩

theorem range_positiveBicollarMap_subset (H : (S × Ioo (-1 : ℝ) 1) ≃ₜ C)
    (hbase : ∀ s, (H (bicollarBase s) : X) = (s : X)) :
    range (positiveBicollarMap H) ⊆ Sᶜ := by
  rintro _ ⟨z, rfl⟩
  exact (bicollar_point_mem_overlap H hbase _ (ne_of_gt z.2.property.1)).1

theorem range_negativeBicollarMap_subset (H : (S × Ioo (-1 : ℝ) 1) ≃ₜ C)
    (hbase : ∀ s, (H (bicollarBase s) : X) = (s : X)) :
    range (negativeBicollarMap H) ⊆ Sᶜ := by
  rintro _ ⟨z, rfl⟩
  exact (bicollar_point_mem_overlap H hbase _ (ne_of_lt z.2.property.2)).1

theorem isConnected_range_positiveBicollarMap [ConnectedSpace S]
    (H : (S × Ioo (-1 : ℝ) 1) ≃ₜ C) : IsConnected (range (positiveBicollarMap H)) := by
  let : ConnectedSpace (Ioo (0 : ℝ) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_Ioo (by norm_num))
  exact isConnected_range (continuous_positiveBicollarMap H)

theorem isConnected_range_negativeBicollarMap [ConnectedSpace S]
    (H : (S × Ioo (-1 : ℝ) 1) ≃ₜ C) : IsConnected (range (negativeBicollarMap H)) := by
  let : ConnectedSpace (Ioo (-1 : ℝ) 0) :=
    isConnected_iff_connectedSpace.mp (isConnected_Ioo (by norm_num))
  exact isConnected_range (continuous_negativeBicollarMap H)

theorem base_subset_closure_positiveBicollarMap (H : (S × Ioo (-1 : ℝ) 1) ≃ₜ C)
    (hbase : ∀ s, (H (bicollarBase s) : X) = (s : X)) :
    S ⊆ closure (range (positiveBicollarMap H)) := by
  intro x hx
  let s : S := ⟨x, hx⟩
  let t0 : Ioo (-1 : ℝ) 1 := ⟨0, by constructor <;> norm_num⟩
  let T : Set (Ioo (-1 : ℝ) 1) := {t | 0 < (t : ℝ)}
  have himage : (Subtype.val : Ioo (-1 : ℝ) 1 → ℝ) '' T = Ioo 0 1 := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨hu, u.property.2⟩
    · intro ht
      exact ⟨⟨t, lt_trans (by norm_num) ht.1, ht.2⟩, ht.1, rfl⟩
  have hzero : t0 ∈ closure T := by
    rw [closure_subtype, himage, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨le_rfl, by norm_num⟩
  have hv : Continuous (fun t : Ioo (-1 : ℝ) 1 => (H (s, t) : X)) :=
    continuous_subtype_val.comp (H.continuous.comp (continuous_const.prodMk continuous_id))
  have hmem := hv.continuousAt.continuousWithinAt.mem_closure hzero
    (fun t ht => mem_range_positiveBicollarMap H (s, t) ht)
  change (H (bicollarBase s) : X) ∈ closure (range (positiveBicollarMap H)) at hmem
  simpa only [hbase] using hmem

theorem base_subset_closure_negativeBicollarMap (H : (S × Ioo (-1 : ℝ) 1) ≃ₜ C)
    (hbase : ∀ s, (H (bicollarBase s) : X) = (s : X)) :
    S ⊆ closure (range (negativeBicollarMap H)) := by
  intro x hx
  let s : S := ⟨x, hx⟩
  let t0 : Ioo (-1 : ℝ) 1 := ⟨0, by constructor <;> norm_num⟩
  let T : Set (Ioo (-1 : ℝ) 1) := {t | (t : ℝ) < 0}
  have himage : (Subtype.val : Ioo (-1 : ℝ) 1 → ℝ) '' T = Ioo (-1) 0 := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.property.1, hu⟩
    · intro ht
      exact ⟨⟨t, ht.1, lt_trans ht.2 (by norm_num)⟩, ht.2, rfl⟩
  have hzero : t0 ∈ closure T := by
    rw [closure_subtype, himage, closure_Ioo (by norm_num : (-1 : ℝ) ≠ 0)]
    exact ⟨by norm_num, le_rfl⟩
  have hv : Continuous (fun t : Ioo (-1 : ℝ) 1 => (H (s, t) : X)) :=
    continuous_subtype_val.comp (H.continuous.comp (continuous_const.prodMk continuous_id))
  have hmem := hv.continuousAt.continuousWithinAt.mem_closure hzero
    (fun t ht => mem_range_negativeBicollarMap H (s, t) ht)
  change (H (bicollarBase s) : X) ∈ closure (range (negativeBicollarMap H)) at hmem
  simpa only [hbase] using hmem

end BrownCollar
