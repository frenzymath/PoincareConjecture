import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false
open Set
namespace PoincareConjecture.M76

theorem exists_collar_slice_homeomorph
    {X A : Type*} [TopologicalSpace X] [TopologicalSpace A] {N : Set X}
    (W : (A × unitInterval) ≃ₜ N) (t : unitInterval) :
    ∃ (B : Set X) (H : A ≃ₜ B), ∀ a, (H a : X) = W (a,t) := by
  let B := range (fun a => (W (a,t) : X))
  let f : A → B := fun a => ⟨W (a,t),⟨a,rfl⟩⟩
  have hBN : B ⊆ N := by rintro _ ⟨a,rfl⟩; exact (W (a,t)).property
  let g : B → A := fun x => (W.symm ⟨x,hBN x.property⟩).1
  have hleft : Function.LeftInverse g f := by
    intro a
    change (W.symm (W (a,t))).1 = a
    rw [W.symm_apply_apply]
  have hright : Function.RightInverse g f := by
    intro x
    obtain ⟨a,ha⟩ := x.property
    have he : f a = x := Subtype.ext ha
    rw [← he,hleft]
  let H : A ≃ₜ B :=
    { toEquiv := ⟨f,g,hleft,hright⟩
      continuous_toFun := by unfold f; fun_prop
      continuous_invFun := by unfold g; fun_prop }
  exact ⟨B,H,fun _ => rfl⟩

theorem exists_prescribed_cut_collar_ports
    {X κ : Type*} [TopologicalSpace X]
    {A : κ → Type*} [∀ i, TopologicalSpace (A i)] {R Q : Set X}
    (O : κ → Set X) (W : ∀ i, (A i × unitInterval) ≃ₜ closure (O i))
    (hQ : Q = R \ ⋃ i,O i) (hCR : ∀ i, closure (O i) ⊆ R)
    (hCC : Pairwise fun i j => Disjoint (closure (O i)) (closure (O j)))
    (hstrip : ∀ i z, (W i z : X) ∈ O i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1) :
    ∃ (B : κ × Bool → Set X) (H : ∀ i b, A i ≃ₜ B (i,b)),
      (∀ i a, (W i (a,0) : X) = H i false a ∧ (W i (a,1) : X) = H i true a) ∧
      (∀ i, closure (O i) ∩ Q = B (i,false) ∪ B (i,true)) ∧
      (∀ b, B b ⊆ frontier Q) ∧ (⋃ i,closure (O i)) ∪ Q = R := by
  classical
  choose B H hH using fun b : κ × Bool =>
    exists_collar_slice_homeomorph (W b.1) (if b.2 then 1 else 0)
  have hBN (i) (b) : B (i,b) ⊆ closure (O i) := by
    intro x hx
    obtain ⟨a,ha⟩ := (H (i,b)).surjective ⟨x,hx⟩
    have he : (W i (a,if b then 1 else 0) : X) = x :=
      (hH (i,b) a).symm.trans (congrArg Subtype.val ha)
    exact he ▸ (W i _).property
  have hBQ (i) (b) : B (i,b) ⊆ Q := by
    intro x hx
    apply hQ.symm.subset
    refine ⟨hCR i (hBN i b hx),?_⟩
    intro hxO
    obtain ⟨j,hj⟩ := mem_iUnion.mp hxO
    by_cases hij : i = j
    · subst j
      obtain ⟨a,ha⟩ := (H (i,b)).surjective ⟨x,hx⟩
      have he : (W i (a,if b then 1 else 0) : X) = x :=
        (hH (i,b) a).symm.trans (congrArg Subtype.val ha)
      have ht := (hstrip i _).mp (he.symm ▸ hj)
      cases b <;> norm_num at ht
    · exact disjoint_left.mp (hCC hij) (hBN i b hx) (subset_closure hj)
  refine ⟨B,fun i b => H (i,b),?_,?_,?_,?_⟩
  · intro i a
    exact ⟨(hH (i,false) a).symm,(hH (i,true) a).symm⟩
  · intro i
    apply subset_antisymm
    · rintro x ⟨hxN,hxQ⟩
      let z := (W i).symm ⟨x,hxN⟩
      have hz : (W i z : X) = x := congrArg Subtype.val ((W i).apply_symm_apply _)
      have hn : ¬ (0 < (z.2 : ℝ) ∧ (z.2 : ℝ) < 1) := by
        intro ht
        exact (hQ.subset hxQ).2 (mem_iUnion.mpr ⟨i,hz ▸ (hstrip i z).mpr ht⟩)
      have hend : z.2 = 0 ∨ z.2 = 1 := by
        have hb := z.2.property
        by_cases he : (z.2 : ℝ) = 0
        · exact Or.inl (Subtype.ext he)
        · have hpos : 0 < (z.2 : ℝ) := lt_of_le_of_ne hb.1 (Ne.symm he)
          have hge : 1 ≤ (z.2 : ℝ) := not_lt.mp (fun ht => hn ⟨hpos,ht⟩)
          exact Or.inr (Subtype.ext (le_antisymm hb.2 hge))
      have hmem (b : Bool) (ht : z.2 = if b then 1 else 0) : x ∈ B (i,b) := by
        have he : (H (i,b) z.1 : X) = x := by rw [hH,← ht]; exact hz
        exact he ▸ (H (i,b) z.1).property
      rcases hend with ht | ht
      · exact Or.inl (hmem false ht)
      · exact Or.inr (hmem true ht)
    · intro x hx
      rcases hx with hx | hx
      · exact ⟨hBN i false hx,hBQ i false hx⟩
      · exact ⟨hBN i true hx,hBQ i true hx⟩
  · intro b x hx
    rw [frontier_eq_closure_inter_closure]
    refine ⟨subset_closure (hBQ b.1 b.2 hx),?_⟩
    apply closure_mono (show O b.1 ⊆ Qᶜ from fun y hy hq =>
      (hQ.subset hq).2 (mem_iUnion.mpr ⟨b.1,hy⟩)) (hBN b.1 b.2 hx)
  · apply subset_antisymm
    · exact union_subset (iUnion_subset hCR) (hQ ▸ sdiff_subset)
    · intro x hx
      by_cases ho : x ∈ ⋃ i,O i
      · exact Or.inl (iUnion_mono (fun _ => subset_closure) ho)
      · exact Or.inr (hQ.symm.subset ⟨hx,ho⟩)

end PoincareConjecture.M76
