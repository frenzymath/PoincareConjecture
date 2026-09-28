import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Regions.OriginalSignedDefiningFunction
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Maps.OriginalLocalScalarExtension
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Maps.OriginalRelativeSigns










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R A U : Set X}



theorem PLDomain.exists_relative_signed_defining_function
    (he : PLDomain e R) (hR : IsCompact R) (heA : PLDomain e A) (hA : IsCompact A)
    (hU : IsOpen U) (hAU : A ⊆ U)
    {f : X → ℝ} (hf : ContinuousOn f U)
    (hfPL : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm)
      ((e i).target ∩ (e i).symm ⁻¹' U))
    (hpos : ∀ x ∈ A, x ∈ interior R ↔ 0 < f x)
    (hzero : ∀ x ∈ A, x ∈ frontier R ↔ f x = 0)
    {r : ℝ} (hr : 0 < r) (hbound : ∀ x ∈ A, |f x| ≤ r) :
    ∃ g : X → ℝ, Continuous g ∧
      (∀ i, LocallyPiecewiseAffineOn (g ∘ (e i).symm) (e i).target) ∧
      EqOn g f A ∧ (∀ x, |g x| ≤ r) ∧
      ∀ x, (x ∈ frontier R ↔ g x = 0) ∧
        (x ∈ interior R ↔ 0 < g x) ∧ (x ∉ R ↔ g x < 0) := by
  obtain ⟨a, _, _, _, hac, ha, haf, habound, _⟩ :=
    OpenPartialHomeomorph.exists_supported_PL_scalar_extension e he.compatible he.cover
      hA hU hAU hf hfPL hr hbound
  obtain ⟨b, hbc, hb, hbsign⟩ := he.exists_signed_defining_function hR
    isOpen_interior.isClosed_compl.isCompact
  have hp (x : X) (hx : x ∈ A) : 0 < a x ↔ 0 < b x := by
    rw [haf hx]
    exact (hpos x hx).symm.trans (hbsign x).2.2.1
  have hz (x : X) (hx : x ∈ A) : a x = 0 ↔ b x = 0 := by
    rw [haf hx]
    exact (hzero x hx).symm.trans (hbsign x).2.1
  obtain ⟨g, hgc, hg, hga, hgsign⟩ := heA.exists_bounded_same_signs_relative hA hbc hac hb ha
    hp hz hr (fun x _ => habound x)
  exact ⟨g, hgc, hg, hga.trans haf, fun x => (hgsign x).1, fun x =>
    ⟨(hbsign x).2.1.trans (hgsign x).2.2.1.symm,
      (hbsign x).2.2.1.trans (hgsign x).2.1.symm,
      (hbsign x).2.2.2.trans (hgsign x).2.2.2.symm⟩⟩

end PoincareConjecture.M76
