import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionSphericalBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLPrescribedBoundaryArc

set_option autoImplicit false

open Set Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsFinitePLBallPair.interval_prism_rim_arcs
    {s : Set E} {a b : E} (hs : IsFinitePLBallPair ℝ s {a, b}) (hab : a ≠ b)
    {α β : ℝ} (hαβ : α < β) (j : Bool) :
    let t := if j then β else α
    let u := if j then α else β
    IsFinitePLBallPair ℝ (s ×ˢ {t}) {(a, t), (b, t)} ∧
      IsFinitePLBallPair ℝ (({a, b} ×ˢ Icc α β) ∪ (s ×ˢ {u})) {(a, t), (b, t)} ∧
      (s ×ˢ {t}) ∪ (({a, b} ×ˢ Icc α β) ∪ (s ×ˢ {u})) =
        ({a, b} ×ˢ Icc α β) ∪ (s ×ˢ {α, β}) ∧
      (s ×ˢ {t}) ∩ (({a, b} ×ˢ Icc α β) ∪ (s ×ˢ {u})) =
        {(a, t), (b, t)} := by
  let t := if j then β else α
  let u := if j then α else β
  let A := s ×ˢ {t}
  let W := ({a, b} ×ˢ Icc α β) ∪ (s ×ˢ {u})
  let Q := ({a, b} ×ˢ Icc α β) ∪ (s ×ˢ {α, β})
  let Z := ({(a, t), (b, t)} : Set (E × ℝ))
  have htm : t ∈ Icc α β := by cases j <;> simp [t, hαβ.le]
  have htu : t ≠ u := by cases j <;> simp [t, u, hαβ.ne, hαβ.ne']
  have hside : IsFinitePLBallPair ℝ A Z := by
    have h := hs.prod_singleton t
    have he : ({a, b} : Set E) ×ˢ {t} = Z := by
      ext x
      simp only [Z, mem_prod, mem_insert_iff, mem_singleton_iff, Prod.ext_iff]
      tauto
    rw [he] at h
    exact h
  have hrect : IsFinitePLBallPair (ℝ × ℝ) (s ×ˢ Icc α β) Q :=
    hs.prod (isFinitePLBallPair_Icc hαβ)
  have hcover : A ∪ W = Q := by
    ext x
    cases j <;> simp only [A, W, Q, t, u, Bool.false_eq_true, ite_false, ite_true,
      mem_union, mem_prod, mem_insert_iff, mem_singleton_iff] <;> tauto
  have hinter : A ∩ W = Z := by
    ext x
    constructor
    · rintro ⟨hxA, hxW | hxW⟩
      · rcases hxW.1 with ha | hb
        · exact Or.inl (Prod.ext ha hxA.2)
        · exact Or.inr (Prod.ext hb hxA.2)
      · exact False.elim (htu (hxA.2.symm.trans hxW.2))
    · rintro (rfl | rfl)
      · exact ⟨⟨hs.1 (Or.inl rfl), rfl⟩, Or.inl ⟨Or.inl rfl, htm⟩⟩
      · exact ⟨⟨hs.1 (Or.inr rfl), rfl⟩, Or.inl ⟨Or.inr rfl, htm⟩⟩
  have hne : (a, t) ≠ (b, t) := fun he => hab (congrArg Prod.fst he)
  obtain ⟨V, hV, hAV, hIV⟩ := hrect.exists_boundary_arc_complement hside
    (subset_union_left.trans hcover.subset) hne
  have hVW : V = W := by
    ext x
    have hc := Set.ext_iff.mp hcover x
    have hi := Set.ext_iff.mp hinter x
    have hcV := Set.ext_iff.mp hAV x
    have hiV := Set.ext_iff.mp hIV x
    change (x ∈ A ∨ x ∈ W) ↔ x ∈ Q at hc
    change (x ∈ A ∧ x ∈ W) ↔ x ∈ Z at hi
    change (x ∈ A ∨ x ∈ V) ↔ x ∈ Q at hcV
    change (x ∈ A ∧ x ∈ V) ↔ x ∈ Z at hiV
    by_cases hxA : x ∈ A
    · constructor
      · exact fun hx => (hi.mpr (hiV.mp ⟨hxA, hx⟩)).2
      · exact fun hx => (hiV.mpr (hi.mp ⟨hxA, hx⟩)).2
    · constructor
      · exact fun hx => (hc.mpr (hcV.mp (Or.inr hx))).resolve_left hxA
      · exact fun hx => (hcV.mpr (hc.mp (Or.inr hx))).resolve_left hxA
  have hW : IsFinitePLBallPair ℝ W Z := by
    rw [← hVW]
    exact hV
  exact ⟨hside, hW, hcover, hinter⟩

end Set
