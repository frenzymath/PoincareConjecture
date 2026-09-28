import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

set_option autoImplicit false

open Set

namespace AddCircle

def closedIntervalArc (p a b : ℝ) : Set (AddCircle p) :=
  (fun t : ℝ => (t : AddCircle p)) '' Icc a b

theorem isCompact_closedIntervalArc (p a b : ℝ) :
    IsCompact (closedIntervalArc p a b) :=
  isCompact_Icc.image (AddCircle.continuous_mk' p)

theorem coe_mem_closedIntervalArc_iff (p : ℝ) [Fact (0 < p)]
    {a b z : ℝ} (ha : 0 ≤ a) (hb : b < p) (hz : z ∈ Ico 0 p) :
    (z : AddCircle p) ∈ closedIntervalArc p a b ↔ z ∈ Icc a b := by
  constructor
  · rintro ⟨t, ht, htz⟩
    have htI : t ∈ Ico (0 : ℝ) (0 + p) :=
      ⟨ha.trans ht.1, by simpa only [zero_add] using ht.2.trans_lt hb⟩
    have hzI : z ∈ Ico (0 : ℝ) (0 + p) := by simpa only [zero_add] using hz
    have htz' : t = z := (coe_eq_coe_iff_of_mem_Ico htI hzI).mp htz
    exact htz' ▸ ht
  · exact fun h => ⟨z, h, rfl⟩

theorem isImage_closedIntervalArc (p : ℝ) [Fact (0 < p)]
    {a b : ℝ} (ha : 0 ≤ a) (hb : b < p) :
    (openPartialHomeomorphCoe p 0).IsImage (Icc a b) (closedIntervalArc p a b) := by
  intro z hz
  have hzI : z ∈ Ico (0 : ℝ) p := by
    change z ∈ Ioo 0 (0 + p) at hz
    exact ⟨hz.1.le, by simpa only [zero_add] using hz.2⟩
  exact coe_mem_closedIntervalArc_iff p ha hb hzI

theorem interior_closedIntervalArc (p : ℝ) [Fact (0 < p)]
    {a b : ℝ} (ha : 0 < a) (hb : b < p) :
    interior (closedIntervalArc p a b) =
      (fun t : ℝ => (t : AddCircle p)) '' Ioo a b := by
  let J := openPartialHomeomorphCoe p 0
  have hJ := isImage_closedIntervalArc p ha.le hb
  have hsource {t : ℝ} (ht : t ∈ Icc a b) : t ∈ J.source := by
    change t ∈ Ioo 0 (0 + p)
    exact ⟨ha.trans_le ht.1, by simpa only [zero_add] using ht.2.trans_lt hb⟩
  ext c
  constructor
  · intro hc
    obtain ⟨t, ht, rfl⟩ := interior_subset hc
    have ht' := (hJ.interior.apply_mem_iff (hsource ht)).mp hc
    rw [interior_Icc] at ht'
    exact ⟨t, ht', rfl⟩
  · rintro ⟨t, ht, rfl⟩
    apply (hJ.interior.apply_mem_iff (hsource ⟨ht.1.le, ht.2.le⟩)).mpr
    simpa only [interior_Icc] using ht

theorem frontier_closedIntervalArc (p : ℝ) [Fact (0 < p)]
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < p) :
    frontier (closedIntervalArc p a b) = {(a : AddCircle p), (b : AddCircle p)} := by
  let J := openPartialHomeomorphCoe p 0
  have hJ := isImage_closedIntervalArc p ha.le hb
  have hsource {t : ℝ} (ht : t ∈ Icc a b) : t ∈ J.source := by
    change t ∈ Ioo 0 (0 + p)
    exact ⟨ha.trans_le ht.1, by simpa only [zero_add] using ht.2.trans_lt hb⟩
  ext c
  constructor
  · intro hc
    obtain ⟨t, ht, rfl⟩ := (isCompact_closedIntervalArc p a b).isClosed.frontier_subset hc
    have ht' := (hJ.frontier.apply_mem_iff (hsource ht)).mp hc
    rw [frontier_Icc hab] at ht'
    rcases ht' with ht' | ht'
    · exact Or.inl (congrArg (fun t : ℝ => (t : AddCircle p)) ht')
    · exact Or.inr (congrArg (fun t : ℝ => (t : AddCircle p)) ht')
  · intro hc
    rcases hc with hc | hc
    · rw [hc]
      apply (hJ.frontier.apply_mem_iff (hsource ⟨le_rfl, hab⟩)).mpr
      rw [frontier_Icc hab]
      exact Or.inl rfl
    · rw [hc]
      apply (hJ.frontier.apply_mem_iff (hsource ⟨hab, le_rfl⟩)).mpr
      rw [frontier_Icc hab]
      exact Or.inr rfl

theorem zero_notMem_closedIntervalArc (p : ℝ) [Fact (0 < p)]
    {a b : ℝ} (ha : 0 < a) (hb : b < p) :
    (0 : AddCircle p) ∉ closedIntervalArc p a b := by
  have hp : 0 < p := Fact.out
  have h := coe_mem_closedIntervalArc_iff p ha.le hb (z := 0) ⟨le_rfl, hp⟩
  intro hz
  have hza : a ≤ 0 := (h.mp hz).1
  exact (not_le_of_gt ha) hza

theorem bounded_add_phase_eq (p : ℝ) [Fact (0 < p)]
    {rm rp u : ℝ} (hm : 0 < rm) (hp : 0 < rp)
    (hsum : rm + rp < p) (hu : -rm ≤ u ∧ u ≤ rp) (a : ℝ) :
    (a : AddCircle p) + (u : AddCircle p) = a ↔ u = 0 := by
  have huI : u ∈ Ico (-rm) (-rm + p) := by constructor <;> linarith [hu.1, hu.2]
  have hzI : (0 : ℝ) ∈ Ico (-rm) (-rm + p) := by constructor <;> linarith
  constructor
  · intro h
    apply (coe_eq_coe_iff_of_mem_Ico huI hzI).mp
    apply add_left_cancel (a := (a : AddCircle p))
    simpa using h
  · rintro rfl
    simp

theorem bounded_sub_phase_eq (p : ℝ) [Fact (0 < p)]
    {rm rp u : ℝ} (hm : 0 < rm) (hp : 0 < rp)
    (hsum : rm + rp < p) (hu : -rm ≤ u ∧ u ≤ rp) (b : ℝ) :
    (b : AddCircle p) - (u : AddCircle p) = b ↔ u = 0 := by
  simpa using bounded_add_phase_eq p hm hp hsum hu 0

theorem bounded_add_mem_closedIntervalArc (p : ℝ) [Fact (0 < p)]
    {rm rp u a b : ℝ} (hm : 0 < rm) (hu : -rm ≤ u ∧ u ≤ rp)
    (hpgap : rp < b - a) (hmgap : rm < p - (b - a)) :
    (a : AddCircle p) + (u : AddCircle p) ∈ closedIntervalArc p a b ↔ 0 ≤ u := by
  have huI : a + u ∈ Ico (a - rm) (a - rm + p) := by
    constructor <;> linarith [hu.1, hu.2]
  constructor
  · rintro ⟨t, ht, htu⟩
    have htI : t ∈ Ico (a - rm) (a - rm + p) := by
      constructor <;> linarith [ht.1, ht.2]
    rw [← coe_add] at htu
    have heq := (coe_eq_coe_iff_of_mem_Ico htI huI).mp htu
    linarith [ht.1]
  · intro h
    exact ⟨a + u, ⟨by linarith, by linarith [hu.2]⟩, coe_add _ _ _⟩

theorem bounded_sub_mem_closedIntervalArc (p : ℝ) [Fact (0 < p)]
    {rm rp u a b : ℝ} (hm : 0 < rm) (hu : -rm ≤ u ∧ u ≤ rp)
    (hpgap : rp < b - a) (hmgap : rm < p - (b - a)) :
    (b : AddCircle p) - (u : AddCircle p) ∈ closedIntervalArc p a b ↔ 0 ≤ u := by
  have huI : b - u ∈ Ioc (b + rm - p) (b + rm - p + p) := by
    constructor <;> linarith [hu.1, hu.2]
  constructor
  · rintro ⟨t, ht, htu⟩
    have htI : t ∈ Ioc (b + rm - p) (b + rm - p + p) := by
      constructor <;> linarith [ht.1, ht.2]
    rw [← coe_sub] at htu
    have heq := (coe_eq_coe_iff_of_mem_Ioc htI huI).mp htu
    linarith [ht.2]
  · intro h
    exact ⟨b - u, ⟨by linarith [hu.2], by linarith⟩, coe_sub _ _ _⟩

end AddCircle
