import Mathlib.Data.List.Chain










set_option autoImplicit false

universe u v

namespace List




theorem exists_consistent_lift {α : Type u} {β : Type v}
    (l : List α) (C : α → β → Prop) (R : α → α → Prop)
    (E : α → β → α → β → Prop)
    (hl : l.IsChain R)
    (hvertex : ∀ a ∈ l, ∃ u, C a u)
    (hedge : ∀ a ∈ l, ∀ b ∈ l, R a b →
      ∃ u v, C a u ∧ C b v ∧ E a u b v)
    (hcompat : ∀ a ∈ l, ∀ b ∈ l, ∀ c ∈ l, ∀ u v w z,
      R a b → R b c → E a u b v → E b w c z → v = w) :
    ∃ q : List (α × β), q.map Prod.fst = l ∧
      (∀ p ∈ q, C p.1 p.2) ∧
      q.IsChain (fun p q => E p.1 p.2 q.1 q.2) := by
  revert hl hvertex hedge hcompat
  induction l using List.twoStepInduction with
  | nil =>
    intro _ _ _ _
    refine ⟨[], rfl, ?_, IsChain.nil⟩
    intro p hp
    cases hp
  | singleton a =>
    intro _ hvertex _ _
    obtain ⟨u₀, hu₀⟩ := hvertex a (by simp)
    refine ⟨[(a, u₀)], rfl, ?_, IsChain.singleton _⟩
    intro p hp
    rcases List.mem_singleton.mp hp with rfl
    exact hu₀
  | cons_cons a b l _ ihtail =>
    intro hl hvertex hedge hcompat
    obtain ⟨hab, htail⟩ := List.isChain_cons_cons.mp hl
    have ha : a ∈ a :: b :: l := List.mem_cons_self
    have hb : b ∈ a :: b :: l := List.mem_cons_of_mem a List.mem_cons_self
    obtain ⟨u₀, v₀, hu₀, hv₀, huv⟩ := hedge a ha b hb hab
    cases l with
    | nil =>
      refine ⟨[(a, u₀), (b, v₀)], rfl, ?_, List.isChain_pair.mpr huv⟩
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hu₀
      · rcases List.mem_singleton.mp hp with rfl
        exact hv₀
    | cons c l =>
      have hc : c ∈ a :: b :: c :: l :=
        List.mem_cons_of_mem a (List.mem_cons_of_mem b List.mem_cons_self)
      have hbc : R b c := (List.isChain_cons_cons.mp htail).1
      obtain ⟨q, hqmap, hqC, hqE⟩ := ihtail b htail
        (fun x hx => hvertex x (List.mem_cons_of_mem a hx))
        (fun x hx y hy => hedge x (List.mem_cons_of_mem a hx)
          y (List.mem_cons_of_mem a hy))
        (fun x hx y hy z hz => hcompat x (List.mem_cons_of_mem a hx)
          y (List.mem_cons_of_mem a hy) z (List.mem_cons_of_mem a hz))
      cases q with
      | nil => simp at hqmap
      | cons p q =>
        cases q with
        | nil => simp at hqmap
        | cons r q =>
          have hp : p.1 = b := (List.cons.inj hqmap).1
          have hr : r.1 = c := (List.cons.inj (List.cons.inj hqmap).2).1
          have hEbc : E b p.2 c r.2 := by
            have hfirst := (List.isChain_cons_cons.mp hqE).1
            change E p.1 p.2 r.1 r.2 at hfirst
            rw [hp, hr] at hfirst
            exact hfirst
          have hlabel : v₀ = p.2 :=
            hcompat a ha b hb c hc u₀ v₀ p.2 r.2 hab hbc huv hEbc
          refine ⟨(a, u₀) :: p :: r :: q, ?_, ?_, ?_⟩
          · change a :: (p :: r :: q).map Prod.fst = a :: b :: c :: l
            exact congrArg (List.cons a) hqmap
          · intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact hu₀
            · exact hqC x hx
          · apply List.isChain_cons_cons.mpr
            refine ⟨?_, hqE⟩
            change E a u₀ p.1 p.2
            rw [hp, ← hlabel]
            exact huv

end List
