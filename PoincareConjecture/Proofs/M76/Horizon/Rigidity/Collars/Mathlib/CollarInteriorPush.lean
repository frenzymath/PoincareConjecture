import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.ClosedProductPasting
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.EmbeddedInverse
import Mathlib.Topology.UnitInterval

set_option autoImplicit false
open Set

namespace Poincare.Topology

theorem exists_collar_interior_push
    {E X : Type*} [TopologicalSpace E] [Zero E]
    [TopologicalSpace X] [T2Space X]
    {K : Set E} (hK : IsCompact K) {r : ℝ} (hr : 0 < r)
    (c : E × ℝ → X) (hc : ContinuousOn c (K ×ˢ Icc (0 : ℝ) r))
    (hi : Topology.IsEmbedding (fun z : (K ×ˢ Icc (0 : ℝ) r : Set (E × ℝ)) => c z))
    (ho : IsOpen (c '' (K ×ˢ Ico (0 : ℝ) r))) :
    ∃ D : C(unitInterval × X, X),
      (∀ y, D (0, y) = y) ∧
      (∀ (t : unitInterval) z, z ∈ K ×ˢ Icc (0 : ℝ) r →
        D (t, c z) = c (z.1, (1 - (t : ℝ)) * z.2 + t * max z.2 (r / 2))) ∧
      (∀ (t : unitInterval) y, y ∉ c '' (K ×ˢ Ico (0 : ℝ) (r / 2)) → D (t, y) = y) ∧
      (∀ y, D (1, y) ∉ c '' (K ×ˢ ({0} : Set ℝ))) ∧
      ∀ (t : unitInterval) y, y ∉ c '' (K ×ˢ ({0} : Set ℝ)) →
        D (t, y) ∉ c '' (K ×ˢ ({0} : Set ℝ)) := by
  let P := K ×ˢ Icc (0 : ℝ) r
  let A := c '' P
  have hA : IsCompact A := (hK.prod isCompact_Icc).image_of_continuousOn hc
  obtain ⟨k, hk, hleft, _, hkmap⟩ := hi.exists_inverse_on_image
  let move (t : unitInterval) (s : ℝ) := (1 - (t : ℝ)) * s + t * max s (r / 2)
  have hmove (t : unitInterval) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) r) :
      move t s ∈ Icc (0 : ℝ) r := by
    have hm0 : 0 ≤ max s (r / 2) := hs.1.trans (le_max_left _ _)
    have hmr : max s (r / 2) ≤ r := max_le hs.2 (by linarith)
    have ht := t.property
    constructor <;> dsimp [move]
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) hs.1) (mul_nonneg ht.1 hm0)
    · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hs.2),
        mul_nonneg ht.1 (sub_nonneg.mpr hmr)]
  have hfixedheight (t : unitInterval) {s : ℝ} (hs : r / 2 ≤ s) : move t s = s := by
    dsimp [move]
    rw [max_eq_left hs]
    ring
  have hkm : Continuous (fun z : unitInterval × A => k z.2) :=
    hk.domRestrict.comp continuous_snd
  let q : unitInterval × A → P := fun z =>
    ⟨((k z.2).1, move z.1 (k z.2).2), (hkmap z.2.property).1,
      hmove z.1 (hkmap z.2.property).2⟩
  have hq : Continuous q := by
    have ht : Continuous (fun z : unitInterval × A => (z.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    exact (hkm.fst.prodMk (((continuous_const.sub ht).mul hkm.snd).add
      (ht.mul (hkm.snd.max continuous_const)))).subtype_mk _
  let G : C(unitInterval × A, X) := ⟨fun z => c (q z), hc.domRestrict.comp hq⟩
  let H : C(unitInterval × X, X) := ⟨Prod.snd, continuous_snd⟩
  have hfront : ∀ (t : unitInterval) (y : A), (y : X) ∈ frontier A →
      G (t, y) = H (t, y) := by
    intro t y hy
    obtain ⟨z, hz, hzy⟩ := y.property
    have hzR : z.2 = r := by
      by_contra hne
      have hzlt : z.2 < r := lt_of_le_of_ne hz.2.2 hne
      have hyint : (y : X) ∈ interior A :=
        (ho.subset_interior_iff.mpr (image_mono (prod_mono Subset.rfl Ico_subset_Icc_self)))
          ⟨z, ⟨hz.1, hz.2.1, hzlt⟩, hzy⟩
      exact disjoint_left.mp disjoint_interior_frontier hyint hy
    change c ((k y).1, move t (k y).2) = (y : X)
    rw [← hzy, hleft z hz, hfixedheight t (show r / 2 ≤ z.2 by rw [hzR]; linarith)]
  obtain ⟨D, hinner, houter⟩ :=
    ContinuousMap.exists_paste_of_eq_on_frontier hA.isClosed G H hfront
  have hvalue (t : unitInterval) (z : E × ℝ) (hz : z ∈ P) :
      D (t, c z) = c (z.1, move t z.2) := by
    have h := hinner t ⟨c z, ⟨z, hz, rfl⟩⟩
    change D (t, c z) = c ((k (c z)).1, move t (k (c z)).2) at h
    simpa only [hleft z hz] using h
  have hnonzero {z : E × ℝ} (hz : z ∈ P) (hpos : 0 < z.2) :
      c z ∉ c '' (K ×ˢ ({0} : Set ℝ)) := by
    rintro ⟨w, hw, hweq⟩
    have hw0 : w.2 = 0 := hw.2
    have hwP : w ∈ P := ⟨hw.1, by rw [hw0]; exact ⟨le_rfl, hr.le⟩⟩
    have heq := congrArg (fun a : P => a.val.2) (hi.injective
      (show c (⟨w, hwP⟩ : P) = c (⟨z, hz⟩ : P) from hweq))
    change w.2 = z.2 at heq
    linarith
  refine ⟨D, ?_, hvalue, ?_, ?_, ?_⟩
  · intro y
    by_cases hy : y ∈ A
    · obtain ⟨z, hz, rfl⟩ := hy
      rw [hvalue 0 z hz]
      simp [move]
    · exact houter 0 y (fun h => hy (interior_subset h))
  · intro t y hy
    by_cases hyA : y ∈ A
    · obtain ⟨z, hz, rfl⟩ := hyA
      have hle : r / 2 ≤ z.2 := by
        by_contra h
        exact hy ⟨z, ⟨hz.1, hz.2.1, lt_of_not_ge h⟩, rfl⟩
      rw [hvalue t z hz, hfixedheight t hle]
    · exact houter t y (fun h => hyA (interior_subset h))
  · intro y
    by_cases hy : y ∈ A
    · obtain ⟨z, hz, rfl⟩ := hy
      rw [hvalue 1 z hz]
      apply hnonzero (z := (z.1, move 1 z.2)) ⟨hz.1, hmove 1 hz.2⟩
      simpa [move] using lt_of_lt_of_le (by linarith : 0 < r / 2) (le_max_right z.2 (r / 2))
    · rw [houter 1 y (fun h => hy (interior_subset h))]
      rintro ⟨z, hz, rfl⟩
      exact hy ⟨z, ⟨hz.1, by rw [show z.2 = 0 from hz.2]; exact ⟨le_rfl, hr.le⟩⟩, rfl⟩
  · intro t y hy
    by_cases hyA : y ∈ A
    · obtain ⟨z, hz, rfl⟩ := hyA
      have hzpos : 0 < z.2 := by
        apply lt_of_le_of_ne hz.2.1
        intro heq
        exact hy ⟨z, ⟨hz.1, heq.symm⟩, rfl⟩
      rw [hvalue t z hz]
      apply hnonzero (z := (z.1, move t z.2)) ⟨hz.1, hmove t hz.2⟩
      have ht := t.property
      have hm := le_max_left z.2 (r / 2)
      dsimp [move]
      nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hm)]
    · rwa [houter t y (fun h => hyA (interior_subset h))]

end Poincare.Topology
