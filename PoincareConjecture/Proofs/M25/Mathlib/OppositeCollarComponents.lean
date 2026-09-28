import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Separation.Collar
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

open Set Topology

namespace Poincare.Topology

variable {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]

theorem closure_connectedComponentIn_compl_subset {S : Set X} (hS : IsClosed S)
    (a : X) :
    closure (connectedComponentIn Sᶜ a) ⊆ connectedComponentIn Sᶜ a ∪ S := by
  intro x hx
  by_cases hxS : x ∈ S
  · exact Or.inr hxS
  · left
    obtain ⟨y, hyC, hyA⟩ := mem_closure_iff.mp hx
      (connectedComponentIn Sᶜ x) hS.isOpen_compl.connectedComponentIn
      (mem_connectedComponentIn hxS)
    rw [connectedComponentIn_eq hyA, ← connectedComponentIn_eq hyC]
    exact mem_connectedComponentIn hxS

theorem opposite_collar_components
    {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [ConnectedSpace Y]
    [T2Space X] {r : ℝ} (hr : 0 < r) {U : Set X} (hU : IsOpen U)
    (e : (Y × Ioo (-r) r) ≃ₜ U) {a b : X}
    (ha : a ∉ range (fun y : Y => (e (y, ⟨0, neg_lt_zero.mpr hr, hr⟩) : X)))
    (hb : b ∉ range (fun y : Y => (e (y, ⟨0, neg_lt_zero.mpr hr, hr⟩) : X)))
    (hne : connectedComponentIn
      (range (fun y : Y => (e (y, ⟨0, neg_lt_zero.mpr hr, hr⟩) : X)))ᶜ a ≠
      connectedComponentIn
        (range (fun y : Y => (e (y, ⟨0, neg_lt_zero.mpr hr, hr⟩) : X)))ᶜ b)
    (hfront : range (fun y : Y => (e (y, ⟨0, neg_lt_zero.mpr hr, hr⟩) : X)) ⊆
      frontier (connectedComponentIn
        (range (fun y : Y => (e (y, ⟨0, neg_lt_zero.mpr hr, hr⟩) : X)))ᶜ a) ∩
      frontier (connectedComponentIn
        (range (fun y : Y => (e (y, ⟨0, neg_lt_zero.mpr hr, hr⟩) : X)))ᶜ b)) :
    let S := range (fun y : Y => (e (y, ⟨0, neg_lt_zero.mpr hr, hr⟩) : X))
    let A := connectedComponentIn Sᶜ a
    let B := connectedComponentIn Sᶜ b
    frontier A = S ∧ frontier B = S ∧ IsClopen (A ∪ S ∪ B) ∧
      IsConnected (A ∪ S ∪ B) ∧ A ∪ S ∪ B = connectedComponent a := by
  let S := range (fun y : Y => (e (y, ⟨0, neg_lt_zero.mpr hr, hr⟩) : X))
  let A := connectedComponentIn Sᶜ a
  let B := connectedComponentIn Sᶜ b
  let L := (fun z => (e z : X)) '' {z | (z.2 : ℝ) < 0}
  let R := (fun z => (e z : X)) '' {z | 0 < (z.2 : ℝ)}
  change a ∉ S at ha
  change b ∉ S at hb
  change A ≠ B at hne
  change S ⊆ frontier A ∩ frontier B at hfront
  change frontier A = S ∧ frontier B = S ∧ IsClopen (A ∪ S ∪ B) ∧
    IsConnected (A ∪ S ∪ B) ∧ A ∪ S ∪ B = connectedComponent a
  have hS : IsClosed S := (isCompact_range
    (continuous_subtype_val.comp (e.continuous.comp
      (continuous_id.prodMk continuous_const)))).isClosed
  have hA : IsOpen A := hS.isOpen_compl.connectedComponentIn
  have hB : IsOpen B := hS.isOpen_compl.connectedComponentIn
  have hAc : IsConnected A := isConnected_connectedComponentIn_iff.mpr ha
  have hBc : IsConnected B := isConnected_connectedComponentIn_iff.mpr hb
  have hAS : A ⊆ Sᶜ := connectedComponentIn_subset _ _
  have hBS : B ⊆ Sᶜ := connectedComponentIn_subset _ _
  have hdis : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro x hxA hxB
    exact hne ((connectedComponentIn_eq hxA).trans (connectedComponentIn_eq hxB).symm)
  have hLc : IsConnected L := isConnected_collar_negative hr e
  have hRc : IsConnected R := isConnected_collar_positive hr e
  have hLS : L ⊆ Sᶜ := by
    rintro x ⟨z, hz, rfl⟩ ⟨y, hy⟩
    have he := e.injective (Subtype.ext hy)
    have ht := congrArg (fun w : Y × Ioo (-r) r => (w.2 : ℝ)) he
    exact (ne_of_lt hz) ht.symm
  have hRS : R ⊆ Sᶜ := by
    rintro x ⟨z, hz, rfl⟩ ⟨y, hy⟩
    have he := e.injective (Subtype.ext hy)
    have ht := congrArg (fun w : Y × Ioo (-r) r => (w.2 : ℝ)) he
    exact (ne_of_gt hz) ht.symm
  have hSU : S ⊆ U := by rintro x ⟨y, rfl⟩; exact (e _).property
  have hUcover : U ⊆ L ∪ S ∪ R := by
    intro x hx
    obtain ⟨z, hz⟩ := e.surjective ⟨x, hx⟩
    have hzx := congrArg Subtype.val hz
    rcases lt_trichotomy (z.2 : ℝ) 0 with ht | ht | ht
    · exact Or.inl (Or.inl ⟨z, ht, hzx⟩)
    · left; right
      refine ⟨z.1, ?_⟩
      have he : (z.1, (⟨0, neg_lt_zero.mpr hr, hr⟩ : Ioo (-r) r)) = z :=
        Prod.ext rfl (Subtype.ext ht.symm)
      simpa only [he] using hzx
    · exact Or.inr ⟨z, ht, hzx⟩
  have hmeet (c : X) (hSc : S ⊆ frontier (connectedComponentIn Sᶜ c)) :
      (L ∩ connectedComponentIn Sᶜ c).Nonempty ∨
        (R ∩ connectedComponentIn Sᶜ c).Nonempty := by
    obtain ⟨y⟩ := (inferInstance : Nonempty Y)
    let x : X := e (y, ⟨0, neg_lt_zero.mpr hr, hr⟩)
    have hxS : x ∈ S := ⟨y, rfl⟩
    obtain ⟨z, hzU, hzC⟩ := mem_closure_iff.mp (hSc hxS).1 U hU (hSU hxS)
    rcases hUcover hzU with (hzL | hzS) | hzR
    · exact Or.inl ⟨z, hzL, hzC⟩
    · exact False.elim ((connectedComponentIn_subset Sᶜ c hzC) hzS)
    · exact Or.inr ⟨z, hzR, hzC⟩
  have hside (c : X) {V : Set X} (hc : IsPreconnected V) (hs : V ⊆ Sᶜ)
      (hi : (V ∩ connectedComponentIn Sᶜ c).Nonempty) :
      V ⊆ connectedComponentIn Sᶜ c := by
    obtain ⟨x, hxV, hxC⟩ := hi
    rw [connectedComponentIn_eq hxC]
    exact hc.subset_connectedComponentIn hxV hs
  have hchooseA : L ⊆ A ∨ R ⊆ A :=
    (hmeet a (fun x hx => (hfront hx).1)).imp
      (hside a hLc.isPreconnected hLS) (hside a hRc.isPreconnected hRS)
  have hchooseB : L ⊆ B ∨ R ⊆ B :=
    (hmeet b (fun x hx => (hfront hx).2)).imp
      (hside b hLc.isPreconnected hLS) (hside b hRc.isPreconnected hRS)
  have hUW : U ⊆ A ∪ S ∪ B := by
    rcases hchooseA with hLA | hRA <;> rcases hchooseB with hLB | hRB
    · obtain ⟨x, hx⟩ := hLc.nonempty
      exact False.elim (Set.disjoint_left.mp hdis (hLA hx) (hLB hx))
    · intro x hx
      rcases hUcover hx with (h | h) | h
      · exact Or.inl (Or.inl (hLA h))
      · exact Or.inl (Or.inr h)
      · exact Or.inr (hRB h)
    · intro x hx
      rcases hUcover hx with (h | h) | h
      · exact Or.inr (hLB h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl (hRA h))
    · obtain ⟨x, hx⟩ := hRc.nonempty
      exact False.elim (Set.disjoint_left.mp hdis (hRA hx) (hRB hx))
  have hclA : closure A = A ∪ S := by
    apply Subset.antisymm (closure_connectedComponentIn_compl_subset hS a)
    exact union_subset subset_closure (fun x hx => (hfront hx).1.1)
  have hclB : closure B = B ∪ S := by
    apply Subset.antisymm (closure_connectedComponentIn_compl_subset hS b)
    exact union_subset subset_closure (fun x hx => (hfront hx).2.1)
  have hfrontA : frontier A = S := by
    apply Subset.antisymm ?_ (fun x hx => (hfront hx).1)
    intro x hx
    rcases hclA ▸ hx.1 with hxA | hxS
    · exact False.elim (hx.2 (hA.interior_eq.symm ▸ hxA))
    · exact hxS
  have hfrontB : frontier B = S := by
    apply Subset.antisymm ?_ (fun x hx => (hfront hx).2)
    intro x hx
    rcases hclB ▸ hx.1 with hxB | hxS
    · exact False.elim (hx.2 (hB.interior_eq.symm ▸ hxB))
    · exact hxS
  have hWcl : A ∪ S ∪ B = closure A ∪ closure B := by
    rw [hclA, hclB]
    ext x; simp only [mem_union]; tauto
  have hWop : IsOpen (A ∪ S ∪ B) := by
    have heq : A ∪ S ∪ B = A ∪ U ∪ B := by
      apply Subset.antisymm
      · exact union_subset (union_subset
          (fun _ h => Or.inl (Or.inl h)) (fun _ h => Or.inl (Or.inr (hSU h))))
          (fun _ h => Or.inr h)
      · exact union_subset (union_subset
          (fun _ h => Or.inl (Or.inl h)) hUW) (fun _ h => Or.inr h)
    rw [heq]
    exact (hA.union hU).union hB
  have hW : IsClopen (A ∪ S ∪ B) :=
    ⟨hWcl ▸ isClosed_closure.union isClosed_closure, hWop⟩
  have hWc : IsConnected (A ∪ S ∪ B) := by
    rw [hWcl]
    apply hAc.closure.union ?_ hBc.closure
    obtain ⟨y⟩ := (inferInstance : Nonempty Y)
    exact ⟨e (y, ⟨0, neg_lt_zero.mpr hr, hr⟩),
      (hfront ⟨y, rfl⟩).1.1, (hfront ⟨y, rfl⟩).2.1⟩
  have haW : a ∈ A ∪ S ∪ B := Or.inl (Or.inl (mem_connectedComponentIn ha))
  exact ⟨hfrontA, hfrontB, hW, hWc,
    Subset.antisymm (hWc.subset_connectedComponent haW)
      (hW.connectedComponent_subset haW)⟩

end Poincare.Topology
