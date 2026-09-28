import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.EdgeReconstruction
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.SingleTriangle









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] (K : SimplicialComplex ℝ E)


def retainedSide (G : SimpleGraph (Triangle K)) (T : Finset (Triangle K))
    (s : Triangle K) (e : Finset E) : Prop :=
  s ∈ T ∧ e ∈ K.faces ∧ e.card = 2 ∧ e ⊆ s.val ∧
    ¬ ∃ t ∈ T, G.Adj s t ∧ e ⊆ t.val

@[simp] theorem retainedSide_singleton_iff
    (G : SimpleGraph (Triangle K)) (s t : Triangle K) (e : Finset E) :
    retainedSide K G {s} t e ↔ t = s ∧ e.card = 2 ∧ e ⊆ s.val := by
  constructor
  · rintro ⟨ht, _, he, hes, _⟩
    have hts := Finset.mem_singleton.mp ht
    exact ⟨hts, he, hts ▸ hes⟩
  · rintro ⟨hts, he, hes⟩
    subst t
    refine ⟨Finset.mem_singleton_self _, ?_, he, hes, ?_⟩
    · exact K.down_closed s.property.1 hes (Finset.card_pos.mp (by omega))
    · rintro ⟨u, hu, hsu, _⟩
      have hus := Finset.mem_singleton.mp hu
      exact hsu.ne hus.symm


theorem triangleRim_eq_original_edge_hulls (s : Triangle K) (p : Fin 3 → E)
    (hp : Function.Injective p) (hrange : range p = (s.val : Set E)) :
    triangleRim p = {x | ∃ e : Finset E,
      e ∈ K.faces ∧ e.card = 2 ∧ e ⊆ s.val ∧ x ∈ convexHull ℝ (e : Set E)} := by
  have hmem (i : Fin 3) : p i ∈ s.val := by
    change p i ∈ (s.val : Set E)
    rw [← hrange]
    exact mem_range_self i
  have hside (i j : Fin 3) (hij : i ≠ j) {x : E}
      (hx : x ∈ segment ℝ (p i) (p j)) :
      ∃ e : Finset E, e ∈ K.faces ∧ e.card = 2 ∧ e ⊆ s.val ∧
        x ∈ convexHull ℝ (e : Set E) := by
    have hsub : ({p i, p j} : Finset E) ⊆ s.val := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hmem i, hmem j⟩
    refine ⟨{p i, p j}, K.down_closed s.property.1 hsub (by simp), ?_, hsub, ?_⟩
    · simp [hp.ne hij]
    · simpa only [Finset.coe_pair, convexHull_pair] using hx
  have hsegment (i j : Fin 3) (hij : i ≠ j) :
      segment ℝ (p i) (p j) ⊆ triangleRim p := by
    fin_cases i <;> fin_cases j <;> try exact (hij rfl).elim
    · exact subset_union_left.trans subset_union_left
    · rw [segment_symm]
      exact subset_union_right
    · rw [segment_symm]
      exact subset_union_left.trans subset_union_left
    · exact subset_union_right.trans subset_union_left
    · exact subset_union_right
    · rw [segment_symm]
      exact subset_union_right.trans subset_union_left
  ext x
  constructor
  · rintro ((h01 | h12) | h20)
    · exact hside 0 1 (by decide) h01
    · exact hside 1 2 (by decide) h12
    · exact hside 2 0 (by decide) h20
  · rintro ⟨e, _, he, hes, hxe⟩
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp he
    have ha : a ∈ s.val := hes (by simp)
    have hb : b ∈ s.val := hes (by simp)
    have ha' : a ∈ range p := by rw [hrange]; exact ha
    have hb' : b ∈ range p := by rw [hrange]; exact hb
    obtain ⟨i, rfl⟩ := ha'
    obtain ⟨j, rfl⟩ := hb'
    apply hsegment i j (fun h ↦ hab (congrArg p h))
    simpa only [Finset.coe_pair, convexHull_pair] using hxe


theorem shared_edge_unique {s t : Triangle K} (hne : s ≠ t)
    {e f : Finset E} (he : e.card = 2) (hf : f.card = 2)
    (hes : e ⊆ s.val) (het : e ⊆ t.val) (hfs : f ⊆ s.val) (hft : f ⊆ t.val) :
    e = f := by
  have hcard : (s.val ∩ t.val).card < 3 := by
    by_contra h
    have hi : s.val ∩ t.val = s.val := Finset.eq_of_subset_of_card_le
      Finset.inter_subset_left (by rw [s.property.2]; omega)
    have hst : s.val ⊆ t.val := hi ▸ Finset.inter_subset_right
    have hv : s.val = t.val := Finset.eq_of_subset_of_card_le hst
      (by rw [s.property.2, t.property.2])
    exact hne (Subtype.ext hv)
  have hei : e ⊆ s.val ∩ t.val := Finset.subset_inter hes het
  have hfi : f ⊆ s.val ∩ t.val := Finset.subset_inter hfs hft
  have heq : e = s.val ∩ t.val := Finset.eq_of_subset_of_card_le hei (by omega)
  have hfq : f = s.val ∩ t.val := Finset.eq_of_subset_of_card_le hfi (by omega)
  exact heq.trans hfq.symm


theorem retainedSide_insert_old_iff
    (G : SimpleGraph (Triangle K)) (T : Finset (Triangle K))
    {leaf neighbor s : Triangle K} (hl : leaf ∉ T) (hn : neighbor ∈ T)
    (hln : G.Adj leaf neighbor)
    (hunique : ∀ t ∈ T, G.Adj leaf t → t = neighbor)
    {e₀ e : Finset E} (he₀ : e₀.card = 2) (he₀l : e₀ ⊆ leaf.val)
    (he₀n : e₀ ⊆ neighbor.val) (hs : s ∈ T) :
    retainedSide K G (insert leaf T) s e ↔
      retainedSide K G T s e ∧ ¬ (s = neighbor ∧ e = e₀) := by
  have hlne : leaf ≠ neighbor := fun h ↦ hl (h ▸ hn)
  constructor
  · rintro ⟨_, hef, he, hes, hret⟩
    refine ⟨⟨hs, hef, he, hes, ?_⟩, ?_⟩
    · rintro ⟨t, ht, hst, het⟩
      exact hret ⟨t, Finset.mem_insert_of_mem ht, hst, het⟩
    · rintro ⟨rfl, rfl⟩
      exact hret ⟨leaf, Finset.mem_insert_self _ _, hln.symm, he₀l⟩
  · rintro ⟨⟨_, hef, he, hes, hret⟩, hnot⟩
    refine ⟨Finset.mem_insert_of_mem hs, hef, he, hes, ?_⟩
    rintro ⟨t, ht, hst, het⟩
    rcases Finset.mem_insert.mp ht with rfl | ht
    · have hsn : s = neighbor := hunique s hs hst.symm
      have heq : e = e₀ := shared_edge_unique K hlne he he₀ het (hsn ▸ hes) he₀l he₀n
      exact hnot ⟨hsn, heq⟩
    · exact hret ⟨t, ht, hst, het⟩


theorem retainedSide_insert_leaf_iff
    (G : SimpleGraph (Triangle K)) (T : Finset (Triangle K))
    {leaf neighbor : Triangle K} (hl : leaf ∉ T) (hn : neighbor ∈ T)
    (hln : G.Adj leaf neighbor)
    (hunique : ∀ t ∈ T, G.Adj leaf t → t = neighbor)
    {e₀ e : Finset E} (he₀ : e₀.card = 2) (he₀l : e₀ ⊆ leaf.val)
    (he₀n : e₀ ⊆ neighbor.val) :
    retainedSide K G (insert leaf T) leaf e ↔
      e ∈ K.faces ∧ e.card = 2 ∧ e ⊆ leaf.val ∧ e ≠ e₀ := by
  have hlne : leaf ≠ neighbor := fun h ↦ hl (h ▸ hn)
  constructor
  · rintro ⟨_, hef, he, hes, hret⟩
    refine ⟨hef, he, hes, ?_⟩
    intro heq
    exact hret ⟨neighbor, Finset.mem_insert_of_mem hn, hln, heq ▸ he₀n⟩
  · rintro ⟨hef, he, hel, hne⟩
    refine ⟨Finset.mem_insert_self _ _, hef, he, hel, ?_⟩
    rintro ⟨t, ht, hlt, het⟩
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hlt.ne rfl
    · have htn : t = neighbor := hunique t ht hlt
      exact hne (shared_edge_unique K hlne he he₀ hel (htn ▸ het) he₀l he₀n)


theorem retainedSide_insert_iff
    (G : SimpleGraph (Triangle K)) (T : Finset (Triangle K))
    {leaf neighbor s : Triangle K} (hl : leaf ∉ T) (hn : neighbor ∈ T)
    (hln : G.Adj leaf neighbor)
    (hunique : ∀ t ∈ T, G.Adj leaf t → t = neighbor)
    {e₀ e : Finset E} (he₀ : e₀.card = 2) (he₀l : e₀ ⊆ leaf.val)
    (he₀n : e₀ ⊆ neighbor.val) :
    retainedSide K G (insert leaf T) s e ↔
      (retainedSide K G T s e ∧ ¬ (s = neighbor ∧ e = e₀)) ∨
      (s = leaf ∧ e ∈ K.faces ∧ e.card = 2 ∧ e ⊆ leaf.val ∧ e ≠ e₀) := by
  constructor
  · intro hret
    rcases Finset.mem_insert.mp hret.1 with hsl | hs
    · subst s
      exact Or.inr ⟨rfl, (retainedSide_insert_leaf_iff K G T hl hn hln hunique
        he₀ he₀l he₀n).mp hret⟩
    · exact Or.inl ((retainedSide_insert_old_iff K G T hl hn hln hunique
        he₀ he₀l he₀n hs).mp hret)
  · rintro (hret | ⟨rfl, hret⟩)
    · exact (retainedSide_insert_old_iff K G T hl hn hln hunique
        he₀ he₀l he₀n hret.1.1).mpr hret
    · exact (retainedSide_insert_leaf_iff K G T hl hn hln hunique
        he₀ he₀l he₀n).mpr hret


theorem retainedSide_attaching_edge
    (G : SimpleGraph (Triangle K)) (T : Finset (Triangle K))
    {leaf neighbor : Triangle K} (hl : leaf ∉ T) (hn : neighbor ∈ T)
    {e₀ : Finset E} (he₀ : e₀ ∈ K.faces) (he₀card : e₀.card = 2)
    (hcofaces : ∀ t : Triangle K, e₀ ⊆ t.val ↔ t = leaf ∨ t = neighbor) :
    retainedSide K G T neighbor e₀ := by
  refine ⟨hn, he₀, he₀card, (hcofaces neighbor).mpr (Or.inr rfl), ?_⟩
  rintro ⟨t, ht, hnt, het⟩
  rcases (hcofaces t).mp het with rfl | rfl
  · exact hl ht
  · exact hnt.ne rfl

end PoincareConjecture.M76.OriginalTriangleCopies
