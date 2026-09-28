import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.CutGraphRealization
import Mathlib.Topology.LocallyFinite









set_option autoImplicit false

open Set

namespace PoincareConjecture.M76.CutGraph

variable {X V I : Type*} [TopologicalSpace X]
  [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]



theorem collar_port_iff_height {S : Type*} [TopologicalSpace S]
    {C : Set X} (B : Bool → Set X) (H : ∀ b, S ≃ₜ B b)
    (W : (S × unitInterval) ≃ₜ C)
    (hW : ∀ x, (W (x, 0) : X) = H false x ∧ (W (x, 1) : X) = H true x)
    (b : Bool) (x : C) :
    (x : X) ∈ B b ↔ (W.symm x).2 = if b then 1 else 0 := by
  have hval (s : S) : (W (s, if b then 1 else 0) : X) = H b s := by
    cases b
    · exact (hW s).1
    · exact (hW s).2
  constructor
  · intro hx
    let s := (H b).symm ⟨x, hx⟩
    have he : W (s, if b then 1 else 0) = x := by
      apply Subtype.ext
      rw [hval]
      exact congrArg Subtype.val ((H b).apply_symm_apply ⟨x, hx⟩)
    have hz := congrArg (fun z => (W.symm z).2) he
    simpa only [W.symm_apply_apply] using hz.symm
  · intro ht
    have he : ((W.symm x).1, if b then 1 else 0) = W.symm x := by
      apply Prod.ext
      · rfl
      · exact ht.symm
    have hx : (x : X) = H b (W.symm x).1 := by
      rw [← hval, he, W.apply_symm_apply]
    rw [hx]
    exact (H b (W.symm x).1).property




theorem exists_closed_cut_graph_collapse
    (R : Set X) (D : V → Set X) (C : I → Set X)
    (B : I → Bool → Set X) (ends : I → Bool → V)
    (S : I → Type*) [∀ i, TopologicalSpace (S i)]
    (W : ∀ i, (S i × unitInterval) ≃ₜ C i)
    (hD : ∀ v, IsClosed (D v)) (hC : ∀ i, IsClosed (C i))
    (hDD : Pairwise fun v w => Disjoint (D v) (D w))
    (hCC : Pairwise fun i j => Disjoint (C i) (C j))
    (hcover : (⋃ v, D v) ∪ (⋃ i, C i) = R)
    (hinc : ∀ i v, C i ∩ D v = ⋃ b ∈ {b | ends i b = v}, B i b)
    (hport : ∀ i b (x : C i), (x : X) ∈ B i b ↔
      ((W i).symm x).2 = if b then 1 else 0) :
    ∃ q : C(R, carrier ends),
      (∀ v (x : R), (x : X) ∈ D v → (q x : Ambient V I) = vertex v) ∧
      (∀ i (x : R) (hi : (x : X) ∈ C i),
        q x = edgePath ends i (((W i).symm ⟨x, hi⟩).2)) := by
  classical
  let pieces : V ⊕ I → Set R := fun j =>
    match j with
    | .inl v => {x | (x : X) ∈ D v}
    | .inr i => {x | (x : X) ∈ C i}
  let F : ∀ j, C(pieces j, carrier ends) := fun j =>
    match j with
    | .inl v => ContinuousMap.const _ ⟨vertex v, vertex_mem_carrier ends v⟩
    | .inr i =>
      ⟨fun x => edgePath ends i (((W i).symm ⟨x.val, x.property⟩).2),
        (edgePath ends i).continuous.comp (continuous_snd.comp
          ((W i).symm.continuous.comp
            ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)))⟩
  have hcross (i : I) (v : V) (x : R) (hi : (x : X) ∈ C i)
      (hv : (x : X) ∈ D v) :
      edgePath ends i (((W i).symm ⟨x, hi⟩).2) =
        (⟨vertex v, vertex_mem_carrier ends v⟩ : carrier ends) := by
    obtain ⟨b, hb, hxb⟩ := mem_iUnion₂.mp ((hinc i v).subset ⟨hi, hv⟩)
    change ends i b = v at hb
    have ht := (hport i b ⟨x, hi⟩).mp hxb
    apply Subtype.ext
    cases b
    · simp only [Bool.false_eq_true, if_false, ht, edgePath_zero, hb]
    · simp only [if_true, ht, edgePath_one, hb]
  have hF : ∀ j k (x : R) (hj : x ∈ pieces j) (hk : x ∈ pieces k),
      F j ⟨x, hj⟩ = F k ⟨x, hk⟩ := by
    intro j k x hj hk
    cases j with
    | inl v =>
      cases k with
      | inl w =>
        by_cases hvw : v = w
        · subst w; rfl
        · exact False.elim (Set.disjoint_left.mp (hDD hvw) hj hk)
      | inr i => exact (hcross i v x hk hj).symm
    | inr i =>
      cases k with
      | inl v => exact hcross i v x hj hk
      | inr j =>
        by_cases hij : i = j
        · subst j; rfl
        · exact False.elim (Set.disjoint_left.mp (hCC hij) hj hk)
  have hpieces : ⋃ j, pieces j = univ := by
    apply iUnion_eq_univ_iff.mpr
    intro x
    have hx := hcover.symm.subset x.property
    rcases hx with hx | hx
    · obtain ⟨v, hv⟩ := mem_iUnion.mp hx
      exact ⟨Sum.inl v, hv⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact ⟨Sum.inr i, hi⟩
  let q := Set.liftCover pieces (fun j => F j) hF hpieces
  have hval (j : V ⊕ I) (x : pieces j) : q x = F j x := Set.liftCover_coe x
  have hq : Continuous q := by
    apply (locallyFinite_of_finite pieces).continuous hpieces
    · intro j
      cases j with
      | inl v => exact (hD v).preimage continuous_subtype_val
      | inr i => exact (hC i).preimage continuous_subtype_val
    · intro j
      rw [continuousOn_iff_continuous_domRestrict]
      have he : (pieces j).domRestrict q = F j := funext (hval j)
      rw [he]
      exact (F j).continuous
  refine ⟨⟨q, hq⟩, ?_, ?_⟩
  · intro v x hx
    exact congrArg Subtype.val (hval (Sum.inl v) ⟨x, hx⟩)
  · intro i x hx
    exact hval (Sum.inr i) ⟨x, hx⟩

end PoincareConjecture.M76.CutGraph
