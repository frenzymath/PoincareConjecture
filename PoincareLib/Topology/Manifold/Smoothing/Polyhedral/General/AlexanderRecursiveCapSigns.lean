import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Collars.AlexanderRecursiveCollarSlab
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Collars.CollarBottomImageClosure
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.OrdinaryCapRimSigns

/-!
# Actual ordinary cap signs from the same moved selected collar

Positive coordinates of the selected original collar give upper
approach at its moved rim. The same cap's disk sublevels then give
both signs away from its one birth height. See Alexander 1924,
p. 7 and M76 derivation 256.
-/

set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Strict height on positive selected-fiber coordinates gives
upper approach to every point of the actual moved rim, inside
the literal capped image. See Alexander p. 7 and derivation 256. -/
theorem AlexanderCollarSlab.ordinary_rim_mem_closure_above
    {S s d b : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β t : ℝ}
    (M : AlexanderCollarSlab S A q β)
    (hb : b ⊆ S ∩ {x | A x = 0}) (hqb : q ∉ b)
    (H : E ≃ₜ E)
    (hselected : ∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (M.upper p.1)},
      (p : E × ℝ).1 ∈ b → (M.chart p : E) ∈ s)
    (hstrict : ∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (M.upper p.1)},
      (p : E × ℝ).1 ∈ b → 0 < (p : E × ℝ).2 → t < A (H (M.chart p))) :
    ∀ x ∈ H '' b, x ∈ closure ((H '' (s ∪ d)) ∩ {y | t < A y}) := by
  rintro x ⟨y, hy, rfl⟩
  apply M.chart.collar_bottom_image_mem_closure M.bottom (hb hy)
    (M.upper_pos y (hb hy) (fun heq => hqb (heq ▸ hy))) H H.continuous
  intro p hp hpos
  have hpb : (p : E × ℝ).1 ∈ b := hp.symm ▸ hy
  exact ⟨mem_image_of_mem H (Or.inl (hselected p hpb)), hstrict p hpb hpos⟩

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [FiniteDimensional ℝ E]

/-- One actual ordinary surgery map supplies both height signs at
every cap point off its birth level. The original selected collar,
strict fiber estimate and all cap certificates refer to that same
map. See Alexander p. 7 and M76 derivation 256. -/
theorem AlexanderCollarSlab.ordinary_cap_mem_both_height_closures
    {S s d b : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β t : ℝ}
    (M : AlexanderCollarSlab S A q β)
    (hb : b ⊆ S ∩ {x | A x = 0}) (hqb : q ∉ b)
    (H : E ≃ₜ E) (ht : 0 < t)
    (hselected : ∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (M.upper p.1)},
      (p : E × ℝ).1 ∈ b → (M.chart p : E) ∈ s)
    (hstrict : ∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (M.upper p.1)},
      (p : E × ℝ).1 ∈ b → 0 < (p : E × ℝ).2 → t < A (H (M.chart p)))
    (hcap : IsFinitePLBallPair V (H '' d) (H '' b))
    (hempty : ∀ c : ℝ, c < t * (2 / 3) ∨ t < c →
      (H '' d) ∩ {x | A x = c} = ∅)
    (hlevels : ∀ a : ℝ, a ∈ Ioc (2 / 3) 1 →
      IsFinitePLBallPair V ((H '' d) ∩ {x | A x ≤ t * a})
        ((H '' d) ∩ {x | A x = t * a})) :
    ∀ x ∈ H '' d, A x ≠ t * (2 / 3) →
      x ∈ closure ((H '' (s ∪ d)) ∩ {y | A y < A x}) ∧
        x ∈ closure ((H '' (s ∪ d)) ∩ {y | A x < A y}) := by
  exact fun _ hx hne => ordinary_cap_mem_both_height_closures_of_rim_approach A ht
    hcap (image_mono subset_union_right) hempty hlevels
    (M.ordinary_rim_mem_closure_above hb hqb H hselected hstrict) hx hne

end Geometry
