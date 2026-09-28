import PoincareConjecture.Proofs.M76.Mathlib.FinitePLHomeomorph
import PoincareConjecture.Proofs.M76.Mathlib.UnitBallPairs









set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {s s' b : Set E} {t t' c : Set F} {e : s ≃ₜ t}



theorem IsFinitePL.setCongr (he : e.IsFinitePL) (hs : s = s') (ht : t = t') :
    ((Homeomorph.setCongr hs.symm).trans (e.trans (Homeomorph.setCongr ht))).IsFinitePL := by
  obtain ⟨f, hf, he⟩ := he
  exact ⟨f, hs ▸ hf, fun x => he ⟨x, hs.symm ▸ x.property⟩⟩




theorem IsFinitePL.restrictSubsets [FiniteDimensional ℝ E]
    (he : e.IsFinitePL) (hb : b ⊆ s) (hc : c ⊆ t)
    (hmem : ∀ x : s, (x : E) ∈ b ↔ (e x : F) ∈ c)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hspace : J.space = b) :
    (e.restrictSubsets hb hc hmem).IsFinitePL := by
  obtain ⟨f, hf, he⟩ := he
  refine ⟨f, ?_, fun x => he ⟨x, hb x.property⟩⟩
  rw [← hspace]
  exact hf.restrict J hJ (hspace.subset.trans hb)

end Homeomorph
