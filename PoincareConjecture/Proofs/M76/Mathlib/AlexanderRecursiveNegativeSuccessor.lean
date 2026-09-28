import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveOppositeSuccessor
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveSelectedZero










set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





theorem AlexanderCollarSlab.nonempty_fixed_negative_successor {S : Set E}
    {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ} (M : AlexanderCollarSlab S (-A) q β)
    {n : ℕ} (P : Polygon E (n + 3))
    (hPe : P.HasSimplicialEdges) (hPi : Function.Injective P) (hqP : q ∈ P.boundary ℝ)
    {d s s' : Set E} (hd : IsFinitePLBallPair (ℝ × ℝ) d (P.boundary ℝ))
    (hs : IsFinitePLBallPair (ℝ × ℝ) s (P.boundary ℝ))
    (hs' : IsFinitePLBallPair (ℝ × ℝ) s' (P.boundary ℝ))
    (hunion : s ∪ s' = S) (hinter : s ∩ s' = P.boundary ℝ)
    (hdplane : d ⊆ {x | A x = 0}) (hcap : d ∩ S = P.boundary ℝ)
    (N : SimplicialComplex ℝ E) (hN : N.faces.Finite)
    (hsection : S ∩ {x | A x = 0} = P.boundary ℝ ∪ N.space)
    (hdN : d ∩ N.space ⊆ {q})
    (hside : d ∩ closure ((s ∪ d) ∩ {x | A x < 0}) ⊆ {q})
    (H : E ≃ₜ E) (hraise : ∀ x, A x ≤ A (H x))
    (hneg : ∀ x ∈ (s ∪ d) ∩ {x | A x < 0}, H x = x)
    (hzero : (H '' (s ∪ d)) ∩ {x | A x = 0} =
      (((s ∪ d) ∩ {x | A x = 0}) \ d) ∪ (d ∩ {q})) :
    Nonempty (AlexanderCollarSlab (H '' (s ∪ d)) (-A) q β) := by
  have hdneg : d ⊆ {x | (-A) x = 0} := by
    simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero] using hdplane
  have hsectionNeg : S ∩ {x | (-A) x = 0} = P.boundary ℝ ∪ N.space := by
    simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero] using hsection
  have havoid : d ∩ closure ((s ∪ d) ∩ {x | 0 < (-A) x}) ⊆ {q} := by
    simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_pos] using hside
  have hP : P.boundary ℝ ⊆ S ∩ {x | (-A) x = 0} :=
    subset_union_left.trans hsectionNeg.symm.subset
  have hother := M.opposite_cut_side_of_cap_avoidance P hPe hPi hd hs hs'
    hunion hinter hP havoid
  have hscopy := hs
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨Ks, hKs, hKss, _⟩, _⟩, _⟩ := hscopy
  have hzeroNeg : (H '' (s ∪ d)) ∩ {x | (-A) x = 0} =
      (((s ∪ d) ∩ {x | (-A) x = 0}) \ d) ∪ (d ∩ {q}) := by
    simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero] using hzero
  have hzeroX := hzeroNeg.trans (M.selected_zero_section_eq
    (subset_union_left.trans hunion.subset) hsectionNeg hcap hd.1 hdN (hd.1 hqP))
  exact M.nonempty_opposite_pointed_successor hs.isCompact.isClosed hs'.isCompact.isClosed
    hunion hinter.subset (hs.1 hqP) N Ks hN hKs hKss hsectionNeg
    (fun x hx => hdN ⟨hd.1 hx.1, hx.2⟩) (fun p hp => (hother p hp).2)
    hdneg H (fun x => by
      simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_le_neg_iff] using hraise x)
    (fun x hx hxA => hneg x ⟨Or.inl hx, by
      change A x < 0
      simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_pos] using hxA⟩) hzeroX

end Geometry
