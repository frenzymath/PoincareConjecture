import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveBandTransport

set_option autoImplicit false

open Set

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsFinitePL.exists_heightInterval_restriction
    {N : Set E} {a b α β : ℝ} {d : Icc a b ≃ₜ N} (hd : d.IsFinitePL)
    (A : E →ᵃ[ℝ] ℝ) (hheight : ∀ t, A (d t) = (t : ℝ))
    (hsub : Icc α β ⊆ Icc a b) :
    ∃ c : Icc α β ≃ₜ (N ∩ {x | A x ∈ Icc α β} : Set E),
      c.IsFinitePL ∧ (∀ t, A (c t) = (t : ℝ)) ∧
      ∀ t, (c t : E) = d ⟨t, hsub t.property⟩ := by
  obtain ⟨C, hC, hCval, hCA⟩ :=
    hd.exists_affineBand_restriction (AffineMap.id ℝ ℝ) A hheight α β
  have hsource : Icc a b ∩ {x | (AffineMap.id ℝ ℝ) x ∈ Icc α β} = Icc α β := by
    ext x
    change (x ∈ Icc a b ∧ x ∈ Icc α β) ↔ x ∈ Icc α β
    exact ⟨And.right, fun hx => ⟨hsub hx, hx⟩⟩
  let c := (Homeomorph.setCongr hsource.symm).trans (C.trans (Homeomorph.setCongr rfl))
  exact ⟨c, hC.setCongr hsource rfl, fun t => hCA ⟨t, hsource.symm.subset t.property⟩,
    fun t => hCval ⟨t, hsource.symm.subset t.property⟩⟩

end Homeomorph
