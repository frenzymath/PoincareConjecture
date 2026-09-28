import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Max

set_option autoImplicit false

open Set

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

theorem Preconnected.induce_sdiff_singleton_of_neighbors_reachable
    {s : Set V} (hG : (G.induce s).Preconnected) {v : V} (hv : v ∈ s)
    (hneighbors : ∀ (a : V) (ha : a ∈ s) (hva : G.Adj v a)
      (b : V) (hb : b ∈ s) (hvb : G.Adj v b),
      (G.induce (s \ {v})).Reachable ⟨a, ha, hva.ne.symm⟩ ⟨b, hb, hvb.ne.symm⟩) :
    (G.induce (s \ {v})).Preconnected := by
  classical
  by_cases hne : ∃ w ∈ s, G.Adj v w
  · obtain ⟨w, hw, hvw⟩ := hne
    let r : s → (s \ {v} : Set V) := fun x =>
      if hx : (x : V) = v then ⟨w, hw, hvw.ne.symm⟩ else ⟨x, x.property, hx⟩
    have hedge {x y : s} (hxy : (G.induce s).Adj x y) :
        (G.induce (s \ {v})).Reachable (r x) (r y) := by
      by_cases hx : (x : V) = v
      · have hyv : G.Adj v y := hx ▸ hxy
        have hy : (y : V) ≠ v := hyv.ne.symm
        simpa only [r, dif_pos hx, dif_neg hy] using
          hneighbors w hw hvw y y.property hyv
      · by_cases hy : (y : V) = v
        · have hxv : G.Adj v x := hy ▸ hxy.symm
          simpa only [r, dif_neg hx, dif_pos hy] using
            hneighbors x x.property hxv w hw hvw
        · simp only [r, dif_neg hx, dif_neg hy]
          exact (show (G.induce (s \ {v})).Adj
            ⟨x, x.property, hx⟩ ⟨y, y.property, hy⟩ from hxy).reachable
    have hwalk {x y : s} (p : (G.induce s).Walk x y) :
        (G.induce (s \ {v})).Reachable (r x) (r y) := by
      induction p with
      | nil => exact Reachable.rfl
      | cons h _ ih => exact (hedge h).trans ih
    intro a b
    obtain ⟨p⟩ := hG ⟨a, a.property.1⟩ ⟨b, b.property.1⟩
    have hav : (a : V) ≠ v := a.property.2
    have hbv : (b : V) ≠ v := b.property.2
    simpa only [r, dif_neg hav, dif_neg hbv] using hwalk p
  · intro a b
    have hva : (⟨v, hv⟩ : s) ≠ ⟨a, a.property.1⟩ := by
      intro h
      exact a.property.2 (congrArg Subtype.val h).symm
    obtain ⟨w, hw⟩ := (hG ⟨v, hv⟩ ⟨a, a.property.1⟩).nonempty_neighborSet_left hva
    exact (hne ⟨w, w.property, hw⟩).elim

theorem Preconnected.induce_lt_of_lower_neighbors
    [Finite V] {R : Type*} [LinearOrder R]
    (hG : G.Preconnected) (A : V → R) (hA : Function.Injective A)
    (hjoin : ∀ (v a b : V), G.Adj v a → G.Adj v b →
      ∀ (ha : A a < A v) (hb : A b < A v),
        (G.induce {x | A x < A v}).Reachable ⟨a, ha⟩ ⟨b, hb⟩)
    (c : R) : (G.induce {x | A x < c}).Preconnected := by
  classical
  let : Fintype V := Fintype.ofFinite V
  have hrec (s : Finset V) : (G.induce (s : Set V)).Preconnected →
      (∀ x ∈ s, ∀ y, A y < A x → y ∈ s) →
      (G.induce {x | x ∈ s ∧ A x < c}).Preconnected := by
    refine Finset.strongInductionOn s ?_
    intro s ih hpre hclosed
    rcases s.eq_empty_or_nonempty with rfl | hs
    · intro a
      exact (Finset.notMem_empty _ a.property.1).elim
    obtain ⟨v, hv, hmax⟩ := s.exists_max_image A hs
    by_cases hvc : A v < c
    · let f : G.induce (s : Set V) →g G.induce {x | x ∈ s ∧ A x < c} :=
        { toFun := fun x => ⟨x, x.property, (hmax x x.property).trans_lt hvc⟩
          map_rel' := fun h => h }
      exact hpre.map f (fun x => ⟨⟨x, x.property.1⟩, Subtype.ext rfl⟩)
    have hdelete : (G.induce ((s : Set V) \ {v})).Preconnected := by
      apply hpre.induce_sdiff_singleton_of_neighbors_reachable hv
      intro a ha hva b hb hvb
      have ha' : A a < A v := lt_of_le_of_ne (hmax a ha)
        (fun h => hva.ne (hA h).symm)
      have hb' : A b < A v := lt_of_le_of_ne (hmax b hb)
        (fun h => hvb.ne (hA h).symm)
      let f : G.induce {x | A x < A v} →g G.induce ((s : Set V) \ {v}) :=
        { toFun := fun x => ⟨x, hclosed v hv x x.property,
            fun h => (ne_of_lt x.property) (congrArg A h)⟩
          map_rel' := fun h => h }
      exact (hjoin v a b hva hvb ha' hb').map f
    have hpre' : (G.induce (↑(s.erase v) : Set V)).Preconnected := by
      exact (Finset.coe_erase v s).symm ▸ hdelete
    have hclosed' : ∀ x ∈ s.erase v, ∀ y, A y < A x → y ∈ s.erase v := by
      intro x hx y hy
      have hxs := Finset.mem_of_mem_erase hx
      refine Finset.mem_erase.mpr ⟨?_, hclosed x hxs y hy⟩
      intro hyv
      exact (not_lt_of_ge (hmax x hxs)) (hyv ▸ hy)
    have hresult := ih (s.erase v) (Finset.erase_ssubset hv) hpre' hclosed'
    have hset : {x | x ∈ s.erase v ∧ A x < c} = {x | x ∈ s ∧ A x < c} := by
      ext x
      constructor
      · exact fun hx => ⟨Finset.mem_of_mem_erase hx.1, hx.2⟩
      · intro hx
        exact ⟨Finset.mem_erase.mpr ⟨fun h => hvc (h ▸ hx.2), hx.1⟩, hx.2⟩
    exact hset ▸ hresult
  have huniv : (G.induce (↑(Finset.univ : Finset V) : Set V)).Preconnected := by
    exact (Finset.coe_univ : (↑(Finset.univ : Finset V) : Set V) = univ).symm ▸
      hG.map G.induceUnivIso.symm.toHom G.induceUnivIso.symm.surjective
  have hset : {x | x ∈ (Finset.univ : Finset V) ∧ A x < c} = {x | A x < c} := by
    ext x
    simp only [mem_ofPred_eq, Finset.mem_univ, true_and]
  exact hset ▸ hrec Finset.univ huniv (fun _ _ _ _ => Finset.mem_univ _)

end SimpleGraph
