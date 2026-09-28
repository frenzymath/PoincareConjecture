import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.SelectedHoleComplement










set_option autoImplicit false

open Set Geometry Geometry.CubicalThreeSphere

namespace Set

local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)

theorem selected_hole_punctured_ball {ι : Type*}
    (a r : ι → Set V4) (ha : ∀ i, IsFinitePLBallPair V3 (a i) (r i))
    (haS : ∀ i, a i ⊆ sphere)
    (hopen : ∀ i, IsOpen ((Subtype.val : sphere → V4) ⁻¹' (a i \ r i)))
    (hdis : Pairwise fun i j => Disjoint (a i) (a j)) (i : ι) :
    IsFinitePLBallPair V3 (sphere \ (a i \ r i)) (r i) ∧
      (∀ j : {j : ι // j ≠ i}, a j ⊆ (sphere \ (a i \ r i)) \ r i) ∧
      ((sphere \ (a i \ r i)) \ ⋃ j : {j : ι // j ≠ i}, a j \ r j) =
        sphere \ ⋃ j, a j \ r j ∧
      ∀ j, r j ⊆ sphere \ ⋃ k, a k \ r k := by
  classical
  refine ⟨(ha i).selected_hole_complement (haS i) (hopen i), ?_, ?_, ?_⟩
  · intro j x hx
    have hxi : x ∉ a i := fun hi => disjoint_left.mp (hdis j.property) hx hi
    exact ⟨⟨haS j hx, fun h => hxi h.1⟩, fun hr => hxi ((ha i).1 hr)⟩
  · ext x
    constructor
    · rintro ⟨⟨hxS, hxi⟩, hxother⟩
      refine ⟨hxS, ?_⟩
      intro hxholes
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hxholes
      by_cases hji : j = i
      · exact hxi (hji ▸ hxj)
      · exact hxother (mem_iUnion.mpr ⟨⟨j, hji⟩, hxj⟩)
    · rintro ⟨hxS, hxholes⟩
      refine ⟨⟨hxS, fun hx => hxholes (mem_iUnion.mpr ⟨i, hx⟩)⟩, ?_⟩
      intro hxother
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hxother
      exact hxholes (mem_iUnion.mpr ⟨j, hxj⟩)
  · intro j x hx
    refine ⟨haS j ((ha j).1 hx), ?_⟩
    intro hxholes
    obtain ⟨k, hxk, hxrk⟩ := mem_iUnion.mp hxholes
    by_cases hjk : j = k
    · exact hxrk (hjk ▸ hx)
    · exact disjoint_left.mp (hdis hjk) ((ha j).1 hx) hxk

end Set
