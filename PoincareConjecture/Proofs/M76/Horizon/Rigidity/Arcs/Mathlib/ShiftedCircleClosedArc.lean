import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CircleClosedArc



set_option autoImplicit false
open Set
namespace AddCircle



theorem coe_mem_closedIntervalArc_shifted_iff (p : ℝ) [Fact (0 < p)]
    {c a b z : ℝ} (ha : c ≤ a) (hb : b < c + p) (hz : z ∈ Ico c (c + p)) :
    (z : AddCircle p) ∈ closedIntervalArc p a b ↔ z ∈ Icc a b := by
  constructor
  · rintro ⟨t, ht, htz⟩
    have htI : t ∈ Ico c (c + p) :=
      ⟨ha.trans ht.1, by simpa only using ht.2.trans_lt hb⟩
    have hzI : z ∈ Ico c (c + p) := by simpa only using hz
    have htz' : t = z := (coe_eq_coe_iff_of_mem_Ico htI hzI).mp htz
    exact htz' ▸ ht
  · exact fun h => ⟨z, h, rfl⟩



theorem isImage_closedIntervalArc_shifted (p : ℝ) [Fact (0 < p)]
    {c a b : ℝ} (ha : c ≤ a) (hb : b < c + p) :
    (openPartialHomeomorphCoe p c).IsImage (Icc a b) (closedIntervalArc p a b) := by
  intro z hz
  have hzI : z ∈ Ico c (c + p) := by
    change z ∈ Ioo c (c + p) at hz
    exact ⟨hz.1.le, by simpa only using hz.2⟩
  exact coe_mem_closedIntervalArc_shifted_iff p ha hb hzI



theorem interior_closedIntervalArc_shifted (p : ℝ) [Fact (0 < p)]
    {c a b : ℝ} (ha : c < a) (hb : b < c + p) :
    interior (closedIntervalArc p a b) =
      (fun t : ℝ => (t : AddCircle p)) '' Ioo a b := by
  let J := openPartialHomeomorphCoe p c
  have hJ := isImage_closedIntervalArc_shifted p ha.le hb
  have hsource {t : ℝ} (ht : t ∈ Icc a b) : t ∈ J.source := by
    change t ∈ Ioo c (c + p)
    exact ⟨ha.trans_le ht.1, by simpa only using ht.2.trans_lt hb⟩
  ext z
  constructor
  · intro hc
    obtain ⟨t, ht, rfl⟩ := interior_subset hc
    have ht' := (hJ.interior.apply_mem_iff (hsource ht)).mp hc
    rw [interior_Icc] at ht'
    exact ⟨t, ht', rfl⟩
  · rintro ⟨t, ht, rfl⟩
    apply (hJ.interior.apply_mem_iff (hsource ⟨ht.1.le, ht.2.le⟩)).mpr
    simpa only [interior_Icc] using ht



theorem frontier_closedIntervalArc_shifted (p : ℝ) [Fact (0 < p)]
    {c a b : ℝ} (ha : c < a) (hab : a ≤ b) (hb : b < c + p) :
    frontier (closedIntervalArc p a b) = {(a : AddCircle p), (b : AddCircle p)} := by
  let J := openPartialHomeomorphCoe p c
  have hJ := isImage_closedIntervalArc_shifted p ha.le hb
  have hsource {t : ℝ} (ht : t ∈ Icc a b) : t ∈ J.source := by
    change t ∈ Ioo c (c + p)
    exact ⟨ha.trans_le ht.1, by simpa only using ht.2.trans_lt hb⟩
  ext z
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


theorem closure_interior_closedIntervalArc_shifted (p : ℝ) [Fact (0 < p)]
    {c a b : ℝ} (ha : c < a) (hab : a < b) (hb : b < c + p) :
    closure (interior (closedIntervalArc p a b)) = closedIntervalArc p a b := by
  rw [interior_closedIntervalArc_shifted p ha hb]
  apply subset_antisymm
  · exact closure_minimal (image_mono Ioo_subset_Icc_self)
      (isCompact_closedIntervalArc p a b).isClosed
  · change (fun t : ℝ => (t : AddCircle p)) '' Icc a b ⊆ _
    rw [← closure_Ioo hab.ne]
    exact image_closure_subset_closure_image (AddCircle.continuous_mk' p)

end AddCircle
