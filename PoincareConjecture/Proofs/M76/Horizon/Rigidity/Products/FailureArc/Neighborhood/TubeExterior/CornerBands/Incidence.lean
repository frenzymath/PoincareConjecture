import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.CornerBands.Coordinates

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.TubeExterior.CornerBands

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

theorem mem_square_frontier {r : ℝ} (hr : 0 ≤ r) (z : P2) :
    z ∈ frontier (transverseSquare r) ↔
      z.1 ∈ Icc (-r) r ∧ z.2 ∈ Icc (-r) r ∧
      (z.1 = -r ∨ z.1 = r ∨ z.2 = -r ∨ z.2 = r) := by
  simp only [transverseSquare,frontier_prod_eq,isClosed_Icc.closure_eq,
    frontier_Icc (by linarith : -r ≤ r)]
  simp only [mem_union,mem_prod,mem_insert_iff,mem_singleton_iff,mem_Icc]
  constructor
  · rintro (⟨hx,h | h⟩ | ⟨h | h,hy⟩) <;> subst_vars <;>
      simp_all only <;> aesop
  · rintro ⟨hx,hy,h | h | h | h⟩
    · exact Or.inr ⟨Or.inl h,hy⟩
    · exact Or.inr ⟨Or.inr h,hy⟩
    · exact Or.inl ⟨hx,Or.inl h⟩
    · exact Or.inl ⟨hx,Or.inr h⟩

private theorem coordinate_bounds {r δ x : ℝ} (hδr : δ ≤ r) (b : Bool)
    (hx : sign b * x ∈ Icc (r - δ) r) : x ∈ Icc (-r) r := by
  cases b <;> simp only [sign,Bool.false_eq_true,if_false,if_true,one_mul,neg_one_mul] at hx
  all_goals exact ⟨by linarith [hx.1,hx.2],by linarith [hx.1,hx.2]⟩

private theorem coordinate_endpoint {r x : ℝ} (b : Bool)
    (hx : sign b * x = r) : x = -r ∨ x = r := by
  cases b <;> simp only [sign,Bool.false_eq_true,if_false,if_true,one_mul,neg_one_mul] at hx
  · exact Or.inr hx
  · exact Or.inl (by linarith)

theorem footprint_subset_frontier {r δ : ℝ} (hδ : 0 ≤ δ) (hδr : δ ≤ r)
    (i : Bool × Bool) : footprint r δ i ⊆ frontier (transverseSquare r) := by
  intro z hz
  apply (mem_square_frontier (hδ.trans hδr) z).mpr
  refine ⟨coordinate_bounds hδr i.1 hz.1,coordinate_bounds hδr i.2 hz.2.1,?_⟩
  rcases hz.2.2 with h | h
  · rcases coordinate_endpoint i.1 h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (coordinate_endpoint i.2 h))

theorem band_subset_lateral {r δ : ℝ} (hδ : 0 ≤ δ) (hδr : δ ≤ r)
    (i : Bool × Bool) : band r δ i ⊆ lateral r :=
  prod_mono (footprint_subset_frontier hδ hδr i) Subset.rfl

theorem bandMap_mapsTo_lateral {r δ : ℝ} (hδ : 0 ≤ δ) (hδr : δ ≤ r)
    (i : Bool × Bool) : MapsTo (bandMap r i) (parameter δ) (lateral r) := by
  intro p hp
  exact band_subset_lateral hδ hδr i
    ((bandMap_image hδ i).subset (mem_image_of_mem _ hp))

private theorem sign_eq_of_positive (b c : Bool) {x : ℝ}
    (hb : 0 < sign b * x) (hc : 0 < sign c * x) : b = c := by
  cases b <;> cases c <;> simp only [sign,Bool.false_eq_true,if_false,if_true,
    one_mul,neg_one_mul] at hb hc <;> first | rfl | linarith

theorem footprints_pairwise_disjoint {r δ : ℝ} (hδr : δ < r) :
    Pairwise (fun i j : Bool × Bool => Disjoint (footprint r δ i) (footprint r δ j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro z hi hj
  apply hij
  exact Prod.ext
    (sign_eq_of_positive i.1 j.1 (x := z.1) (by linarith [hi.1.1]) (by linarith [hj.1.1]))
    (sign_eq_of_positive i.2 j.2 (x := z.2) (by linarith [hi.2.1.1]) (by linarith [hj.2.1.1]))

theorem bands_pairwise_disjoint {r δ : ℝ} (hδr : δ < r) :
    Pairwise (fun i j : Bool × Bool => Disjoint (band r δ i) (band r δ j)) := by
  intro i j hij
  exact disjoint_left.mpr (fun z hi hj =>
    disjoint_left.mp (footprints_pairwise_disjoint hδr hij) hi.1 hj.1)

theorem first_sheet_iff {r δ : ℝ} (hδ : 0 ≤ δ) (hδr : δ < r)
    (i : Bool × Bool) {s : ℝ} (hs : s ∈ Icc (-δ) δ) :
    (arcMap r i s).2 = (arcMap r i s).1 ↔ i.1 = i.2 ∧ s = 0 := by
  have h := arcMap_mem_footprint (r := r) hδ (false,false) hs
  have hx : 0 < r - max 0 s := by
    have hh := h.1.1
    simp only [arcMap,sign,if_false,one_mul,Bool.false_eq_true] at hh
    linarith
  have hy : 0 < r + s - max 0 s := by
    have hh := h.2.1.1
    simp only [arcMap,sign,if_false,one_mul,Bool.false_eq_true] at hh
    linarith
  rcases i with ⟨a,b⟩
  cases a <;> cases b <;> simp only [arcMap,sign,Bool.false_eq_true,if_false,if_true,
    one_mul,neg_one_mul,true_and,false_and,Bool.true_eq_false]
  all_goals constructor <;> intro heq <;> first | contradiction | linarith

theorem second_sheet_iff {r δ : ℝ} (hδ : 0 ≤ δ) (hδr : δ < r)
    (i : Bool × Bool) {s : ℝ} (hs : s ∈ Icc (-δ) δ) :
    (arcMap r i s).2 = -(arcMap r i s).1 ↔ i.1 ≠ i.2 ∧ s = 0 := by
  have h := arcMap_mem_footprint (r := r) hδ (false,false) hs
  have hx : 0 < r - max 0 s := by
    have hh := h.1.1
    simp only [arcMap,sign,if_false,one_mul,Bool.false_eq_true] at hh
    linarith
  have hy : 0 < r + s - max 0 s := by
    have hh := h.2.1.1
    simp only [arcMap,sign,if_false,one_mul,Bool.false_eq_true] at hh
    linarith
  rcases i with ⟨a,b⟩
  cases a <;> cases b <;> simp only [arcMap,sign,Bool.false_eq_true,if_false,if_true,
    one_mul,neg_one_mul,true_and,false_and,Bool.true_eq_false,
    ne_eq,not_false_eq_true,not_true_eq_false,neg_neg]
  all_goals constructor <;> intro heq <;> first | contradiction | linarith

end PoincareConjecture.M76.Dehn.Annuli.TubeExterior.CornerBands
