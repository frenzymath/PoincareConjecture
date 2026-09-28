import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Filter Topology

namespace PoincareConjecture.M08

theorem exists_enlarged_closed_interval {a b c d : ℝ} (hab : a < b)
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    {U : Set ℝ} (hU : IsOpen U) (hcore : Icc c d ⊆ U) :
    ∃ l r : ℝ, a ≤ l ∧ l < r ∧ r ≤ b ∧ l ≤ c ∧ d ≤ r ∧ Icc l r ⊆ U ∧
      ∀ s ∈ Icc c d, Icc l r ∈ 𝓝[Icc a b] s := by
  obtain ⟨l₀, u₀, ⟨hlc, hcu⟩, hleft⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds (hcore ⟨le_rfl, hcd⟩))
  obtain ⟨l₁, u₁, ⟨hld, hdu⟩, hright⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds (hcore ⟨hcd, le_rfl⟩))
  let l' := (l₀ + c) / 2
  let r' := (d + u₁) / 2
  have hll : l₀ < l' := by dsimp only [l']; linarith
  have hlc' : l' < c := by dsimp only [l']; linarith
  have hdr' : d < r' := by dsimp only [r']; linarith
  have hrr : r' < u₁ := by dsimp only [r']; linarith
  have henlarged : Icc l' r' ⊆ U := by
    intro s hs
    rcases le_total s c with hsc | hcs
    · exact hleft ⟨hll.trans_le hs.1, hsc.trans_lt hcu⟩
    · rcases le_total d s with hds | hsd
      · exact hright ⟨hld.trans_le hds, hs.2.trans_lt hrr⟩
      · exact hcore ⟨hcs, hsd⟩
  let l := max a l'
  let r := min b r'
  have hlr : l < r := max_lt
    (lt_min hab ((hac.trans hcd).trans_lt hdr'))
    (lt_min ((hlc'.trans_le hcd).trans_le hdb) ((hlc'.trans_le hcd).trans hdr'))
  refine ⟨l, r, le_max_left _ _, hlr, min_le_left _ _, max_le hac hlc'.le,
    le_min hdb hdr'.le, ?_, ?_⟩
  · exact (Icc_subset_Icc (le_max_right _ _) (min_le_right _ _)).trans henlarged
  · intro s hs
    apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
    refine ⟨Ioo l' r', Ioo_mem_nhds (hlc'.trans_le hs.1) (hs.2.trans_lt hdr'), ?_⟩
    intro t ht
    exact ⟨max_le ht.2.1 ht.1.1.le, le_min ht.2.2 ht.1.2.le⟩

theorem exists_overlapping_Icc_partition {ι : Type*} (U : ι → Set ℝ)
    (hU : ∀ i, IsOpen (U i)) {a b : ℝ} (hab : a < b)
    (hcover : Icc a b ⊆ ⋃ i, U i) :
    ∃ (m : ℕ) (t : Fin (m + 1) → ℝ) (c : Fin m → ι) (l r : Fin m → ℝ),
      0 < m ∧ Monotone t ∧ t 0 = a ∧ t (Fin.last m) = b ∧
      ∀ i, a ≤ l i ∧ l i < r i ∧ r i ≤ b ∧ l i ≤ t i.castSucc ∧
        t i.succ ≤ r i ∧ Icc (l i) (r i) ⊆ U (c i) ∧
          ∀ s ∈ Icc (t i.castSucc) (t i.succ), Icc (l i) (r i) ∈ 𝓝[Icc a b] s := by
  classical
  let V : ι → Set (Icc a b) := fun i ↦ (Subtype.val : Icc a b → ℝ) ⁻¹' U i
  have hV : ∀ i, IsOpen (V i) := fun i ↦ (hU i).preimage continuous_subtype_val
  have hVcover : (univ : Set (Icc a b)) ⊆ ⋃ i, V i := by
    intro s _
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover s.property)
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨u, hua, humono, ⟨k, huk⟩, hpieces⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc hab.le hV hVcover
  let m := k + 1
  let t : Fin (m + 1) → ℝ := fun i ↦ u i
  have htm : Monotone t := fun i j hij ↦ humono hij
  have hta : t 0 = a := hua
  have htb : t (Fin.last m) = b := huk m (Nat.le_succ k)
  choose c hc using fun i : Fin m ↦ hpieces i.1
  have hcore (i : Fin m) : Icc (t i.castSucc) (t i.succ) ⊆ U (c i) := by
    intro s hs
    have hsab : s ∈ Icc a b :=
      ⟨(u i.1).property.1.trans hs.1, hs.2.trans (u (i.1 + 1)).property.2⟩
    exact hc i (show (⟨s, hsab⟩ : Icc a b) ∈ Icc (u i.1) (u (i.1 + 1)) from hs)
  choose l r hl using fun i : Fin m ↦ exists_enlarged_closed_interval hab
    (u i.1).property.1 (humono (Nat.le_succ i.1)) (u (i.1 + 1)).property.2
      (hU (c i)) (hcore i)
  exact ⟨m, t, c, l, r, Nat.succ_pos k, htm, hta, htb, hl⟩

end PoincareConjecture.M08
