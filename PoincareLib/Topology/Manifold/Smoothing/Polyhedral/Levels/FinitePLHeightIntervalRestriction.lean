import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.AlexanderRecursiveBandTransport

/-!
# Exact restrictions of finite PL height interval charts

A chart parametrized by actual affine height restricts to the exact
carrier inside any smaller closed height interval. Its old pointwise
values are retained. See Alexander 1924, pp. 6--8 and derivation 268.
-/

set_option autoImplicit false

open Set

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Restrict a finite PL height chart to a smaller closed interval,
retaining its original values. The smaller interval may be empty.
See Alexander pp. 6--8 and M76 derivation 268. -/
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
