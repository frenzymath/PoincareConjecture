import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.CornerBands.Incidence



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.TubeExterior.CornerBands

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

def openFootprint (r δ : ℝ) (i : Bool × Bool) : Set P2 :=
  {z | (sign i.1 * z.1 ∈ Ioc (r - δ) r) ∧
    (sign i.2 * z.2 ∈ Ioc (r - δ) r) ∧
    (sign i.1 * z.1 = r ∨ sign i.2 * z.2 = r)}

def openBand (r δ : ℝ) (i : Bool × Bool) : Set C3 := openFootprint r δ i ×ˢ Icc 0 1

def edgeFootprint (r δ : ℝ) (i : Bool × Bool) : Set P2 :=
  if i.1 then Icc (-r + δ) (r - δ) ×ˢ {sign i.2 * r}
  else {sign i.2 * r} ×ˢ Icc (-r + δ) (r - δ)

def panel (r δ : ℝ) (i : Bool × Bool) : Set C3 := edgeFootprint r δ i ×ˢ Icc 0 1

theorem openFootprint_subset (r δ : ℝ) (i : Bool × Bool) :
    openFootprint r δ i ⊆ footprint r δ i :=
  fun _ hz => ⟨⟨hz.1.1.le,hz.1.2⟩,⟨hz.2.1.1.le,hz.2.1.2⟩,hz.2.2⟩

theorem arcMap_open_image {r δ : ℝ} (hδ : 0 ≤ δ) (i : Bool × Bool) :
    arcMap r i '' Ioo (-δ) δ = openFootprint r δ i := by
  apply Subset.antisymm
  · rintro _ ⟨s,hs,rfl⟩
    have hclosed := arcMap_mem_footprint (r := r) hδ i ⟨hs.1.le,hs.2.le⟩
    refine ⟨⟨?_,hclosed.1.2⟩,⟨?_,hclosed.2.1.2⟩,hclosed.2.2⟩
    · rw [(signed_arcMap r i s).1]
      rcases le_total s 0 with h | h
      · rw [max_eq_left h]
        linarith [hs.1,hs.2]
      · rw [max_eq_right h]
        linarith [hs.2]
    · rw [(signed_arcMap r i s).2]
      rcases le_total s 0 with h | h
      · rw [max_eq_left h]
        linarith [hs.1]
      · rw [max_eq_right h]
        linarith [hs.1,hs.2]
  · intro z hz
    exact ⟨sign i.2 * z.2 - sign i.1 * z.1,
      ⟨by linarith [hz.1.2,hz.2.1.1],by linarith [hz.1.1,hz.2.1.2]⟩,
      arcMap_inverse (openFootprint_subset r δ i hz)⟩

theorem bandMap_open_image {r δ : ℝ} (hδ : 0 ≤ δ) (i : Bool × Bool) :
    bandMap r i '' openParameter δ = openBand r δ i := by
  change Prod.map (arcMap r i) id '' (Ioo (-δ) δ ×ˢ Icc 0 1) = _
  rw [prodMap_image_prod,image_id,arcMap_open_image hδ]
  rfl

private theorem abs_signed (b : Bool) (x : ℝ) : |sign b * x| = |x| := by
  cases b <;> simp [sign]

private theorem exists_abs_sign (x : ℝ) : ∃ b, sign b * x = |x| := by
  by_cases hx : 0 ≤ x
  · exact ⟨false,by simp [sign,abs_of_nonneg hx]⟩
  · exact ⟨true,by simp [sign,abs_of_neg (lt_of_not_ge hx)]⟩

theorem mem_openFootprints_iff {r δ : ℝ} (hδ : 0 ≤ δ) (hδr : δ < r) (z : P2) :
    z ∈ ⋃ i, openFootprint r δ i ↔
      z ∈ frontier (transverseSquare r) ∧ r - δ < |z.1| ∧ r - δ < |z.2| := by
  constructor
  · intro hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    have hp : 0 < sign i.1 * z.1 := by linarith [hi.1.1]
    have hq : 0 < sign i.2 * z.2 := by linarith [hi.2.1.1]
    have hpabs : |z.1| = sign i.1 * z.1 := (abs_signed i.1 z.1).symm.trans (abs_of_pos hp)
    have hqabs : |z.2| = sign i.2 * z.2 := (abs_signed i.2 z.2).symm.trans (abs_of_pos hq)
    exact ⟨footprint_subset_frontier hδ hδr.le i (openFootprint_subset r δ i hi),
      hpabs.symm ▸ hi.1.1,hqabs.symm ▸ hi.2.1.1⟩
  · rintro ⟨hz,hx,hy⟩
    have hr : 0 ≤ r := hδ.trans hδr.le
    obtain ⟨a,ha⟩ := exists_abs_sign z.1
    obtain ⟨b,hb⟩ := exists_abs_sign z.2
    have hh := (mem_square_frontier hr z).mp hz
    have hxle : |z.1| ≤ r := abs_le.mpr hh.1
    have hyle : |z.2| ≤ r := abs_le.mpr hh.2.1
    have hend : |z.1| = r ∨ |z.2| = r := by
      rcases hh.2.2 with h | h | h | h
      · exact Or.inl (by rw [h,abs_neg,abs_of_nonneg hr])
      · exact Or.inl (by rw [h,abs_of_nonneg hr])
      · exact Or.inr (by rw [h,abs_neg,abs_of_nonneg hr])
      · exact Or.inr (by rw [h,abs_of_nonneg hr])
    apply mem_iUnion.mpr
    refine ⟨(a,b),?_⟩
    change (sign a * z.1 ∈ Ioc _ _) ∧ (sign b * z.2 ∈ Ioc _ _) ∧ _
    rw [ha,hb]
    exact ⟨⟨hx,hxle⟩,⟨hy,hyle⟩,hend⟩

theorem mem_edgeFootprints_iff (r δ : ℝ) (z : P2) :
    z ∈ ⋃ i, edgeFootprint r δ i ↔
      ((z.1 = -r ∨ z.1 = r) ∧ z.2 ∈ Icc (-r + δ) (r - δ)) ∨
      (z.1 ∈ Icc (-r + δ) (r - δ) ∧ (z.2 = -r ∨ z.2 = r)) := by
  simp only [mem_iUnion,Prod.exists,Bool.exists_bool,edgeFootprint,sign,
    Bool.false_eq_true,if_false,if_true,one_mul,neg_one_mul,mem_prod,mem_singleton_iff]
  tauto

theorem square_frontier_sdiff_openFootprints {r δ : ℝ} (hδ : 0 < δ) (hδr : δ < r) :
    frontier (transverseSquare r) \ (⋃ i, openFootprint r δ i) = ⋃ i, edgeFootprint r δ i := by
  ext z
  rw [mem_sdiff,mem_openFootprints_iff hδ.le hδr,
    mem_square_frontier (hδ.trans hδr).le,mem_edgeFootprints_iff]
  simp only [mem_Icc]
  constructor
  · rintro ⟨⟨hx,hy,hend⟩,hn⟩
    have hsmall : |z.1| ≤ r - δ ∨ |z.2| ≤ r - δ := by
      by_contra h
      push Not at h
      exact hn ⟨⟨hx,hy,hend⟩,h.1,h.2⟩
    rcases hend with h | h | h | h
    · refine Or.inl ⟨Or.inl h,?_⟩
      rcases hsmall with hs | hs
      · rw [h,abs_neg,abs_of_pos (hδ.trans hδr)] at hs
        linarith
      · have hh := abs_le.mp hs
        constructor <;> linarith [hh.1,hh.2]
    · refine Or.inl ⟨Or.inr h,?_⟩
      rcases hsmall with hs | hs
      · rw [h,abs_of_pos (hδ.trans hδr)] at hs
        linarith
      · have hh := abs_le.mp hs
        constructor <;> linarith [hh.1,hh.2]
    · refine Or.inr ⟨?_,Or.inl h⟩
      rcases hsmall with hs | hs
      · have hh := abs_le.mp hs
        constructor <;> linarith [hh.1,hh.2]
      · rw [h,abs_neg,abs_of_pos (hδ.trans hδr)] at hs
        linarith
    · refine Or.inr ⟨?_,Or.inr h⟩
      rcases hsmall with hs | hs
      · have hh := abs_le.mp hs
        constructor <;> linarith [hh.1,hh.2]
      · rw [h,abs_of_pos (hδ.trans hδr)] at hs
        linarith
  · rintro (⟨h,hlo,hhi⟩ | ⟨⟨hlo,hhi⟩,h⟩)
    · refine ⟨⟨?_,⟨by linarith,by linarith⟩,?_⟩,?_⟩
      · rcases h with h | h <;> rw [h] <;> constructor <;> linarith
      · exact h.elim Or.inl (fun h => Or.inr (Or.inl h))
      · rintro ⟨_,_,hh⟩
        have hs : |z.2| ≤ r - δ := abs_le.mpr ⟨by linarith,hhi⟩
        linarith
    · refine ⟨⟨⟨by linarith,by linarith⟩,?_,Or.inr (Or.inr h)⟩,?_⟩
      · rcases h with h | h <;> rw [h] <;> constructor <;> linarith
      · rintro ⟨_,hh,_⟩
        have hs : |z.1| ≤ r - δ := abs_le.mpr ⟨by linarith,hhi⟩
        linarith

theorem lateral_sdiff_openBands {r δ : ℝ} (hδ : 0 < δ) (hδr : δ < r) :
    lateral r \ (⋃ i, openBand r δ i) = ⋃ i, panel r δ i := by
  ext z
  constructor
  · rintro ⟨hz,hn⟩
    have hh : z.1 ∈ frontier (transverseSquare r) \ (⋃ i, openFootprint r δ i) := by
      refine ⟨hz.1,?_⟩
      intro h
      obtain ⟨i,hi⟩ := mem_iUnion.mp h
      exact hn (mem_iUnion.mpr ⟨i,hi,hz.2⟩)
    obtain ⟨i,hi⟩ := mem_iUnion.mp ((square_frontier_sdiff_openFootprints hδ hδr).subset hh)
    exact mem_iUnion.mpr ⟨i,hi,hz.2⟩
  · intro hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    have hh := (square_frontier_sdiff_openFootprints hδ hδr).symm.subset
      (mem_iUnion.mpr ⟨i,hi.1⟩)
    refine ⟨⟨hh.1,hi.2⟩,?_⟩
    intro h
    obtain ⟨j,hj⟩ := mem_iUnion.mp h
    exact hh.2 (mem_iUnion.mpr ⟨j,hj.1⟩)

theorem lateral_cover {r δ : ℝ} (hδ : 0 < δ) (hδr : δ < r) :
    (⋃ i, band r δ i) ∪ (⋃ i, panel r δ i) = lateral r := by
  rw [← lateral_sdiff_openBands hδ hδr]
  have hb : (⋃ i, band r δ i) ⊆ lateral r :=
    iUnion_subset (fun i => band_subset_lateral hδ.le hδr.le i)
  have ho : (⋃ i, openBand r δ i) ⊆ ⋃ i, band r δ i := by
    apply iUnion_mono
    intro i
    exact prod_mono (openFootprint_subset r δ i) Subset.rfl
  ext z
  constructor
  · exact fun h => h.elim (fun hx => hb hx) (fun hx => hx.1)
  · intro hz
    by_cases hm : z ∈ ⋃ i, band r δ i
    · exact Or.inl hm
    · exact Or.inr ⟨hz,fun h => hm (ho h)⟩

end PoincareConjecture.M76.Dehn.Annuli.TubeExterior.CornerBands
