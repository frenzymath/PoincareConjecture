import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Pasting.RetainedCopy
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.Compactness

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.AnnulusSquareCopies

local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Sq" => (I ×ˢ I : Set P2)

theorem retained_fiber_relation
    {X : Type*} {f : Fin 2 → P2 → X} {g old : P2 → X} {K : Set P2}
    (C : AnnulusSquareCopies f g) (H : Sq ≃ₜ K)
    (hval : ∀ z : Sq, f 0 z = old (H z))
    (hdouble : {x : P2 | x ∈ squareAnnulus 8 1 ∧
        ∃ y ∈ squareAnnulus 8 1, y ≠ x ∧ g y = g x} =
      (fun z : Sq ↦ (C.chart 0 z : P2)) ''
        {u : Sq | ∃ v : Sq, v ≠ u ∧ old (H v) = old (H u)}) :
    {v : P2 × P2 | v.1 ∈ squareAnnulus 8 1 ∧ v.2 ∈ squareAnnulus 8 1 ∧
      g v.1 = g v.2 ∧ v.1 ≠ v.2} =
      (fun v : K × K ↦ (C.retainedDiskCopy H v.1, C.retainedDiskCopy H v.2)) ''
        {v | old v.1 = old v.2 ∧ (v.1 : P2) ≠ v.2} := by
  have hnew := C.double_locus_eq_original_retained H old hdouble
  have hkeep (x : K) : g (C.retainedDiskCopy H x) = old x := by
    change g (C.chart 0 (H.symm x)) = old x
    rw [C.val, hval, Homeomorph.apply_symm_apply]
  ext v
  constructor
  · rintro ⟨hx, hy, hxy, hne⟩
    obtain ⟨a, _, ha⟩ := hnew.subset ⟨hx, v.2, hy, hxy, hne⟩
    obtain ⟨b, _, hb⟩ := hnew.subset ⟨hy, v.1, hx, hxy.symm, hne.symm⟩
    refine ⟨(a, b), ⟨?_, ?_⟩, Prod.ext ha hb⟩
    · rw [← hkeep a, ← hkeep b, ha, hb]
      exact hxy
    · intro he
      exact hne (ha.symm.trans ((congrArg (C.retainedDiskCopy H)
        (Subtype.ext he)).trans hb))
  · rintro ⟨⟨a, b⟩, ⟨hab, hne⟩, rfl⟩
    refine ⟨C.chart_mem 0 (H.symm a), C.chart_mem 0 (H.symm b), ?_, ?_⟩
    · rw [hkeep, hkeep]
      exact hab
    · intro he
      exact hne (congrArg Subtype.val (C.retainedDiskCopy_injective H he))

theorem retained_double_regularity
    {X : Type*} {f : Fin 2 → P2 → X} {g old : P2 → X} {K S : Set P2}
    (C : AnnulusSquareCopies f g) (H : Sq ≃ₜ K)
    (hKS : K ⊆ S) (hK : IsClosed K) (hG : IsCompact (doubleLocusOn old S))
    (p : doubleLocusOn old S → doubleLocusOn old S) (hp : Continuous p)
    (hvalue : ∀ x, old (p x) = old x) (hfree : ∀ x, (p x : P2) ≠ x)
    (hunique : ∀ (x : doubleLocusOn old S) (y : P2), y ∈ S →
      old x = old y → (x : P2) ≠ y → y = (p x : P2))
    (hval : ∀ z : Sq, f 0 z = old (H z))
    (hdouble : {x : P2 | x ∈ squareAnnulus 8 1 ∧
        ∃ y ∈ squareAnnulus 8 1, y ≠ x ∧ g y = g x} =
      (fun z : Sq ↦ (C.chart 0 z : P2)) ''
        {u : Sq | ∃ v : Sq, v ≠ u ∧ old (H v) = old (H u)}) :
    IsCompact (doubleLocusOn g (squareAnnulus 8 1)) ∧
      ∀ a ∈ squareAnnulus 8 1, ∀ b ∈ squareAnnulus 8 1, ∀ d ∈ squareAnnulus 8 1,
        g a = g b → g a = g d → a ≠ b → a ≠ d → b = d := by
  refine ⟨Annuli.isCompact_new_double_locus_of_retained hKS hK hG p hp hvalue hfree
    hunique (C.retainedDiskCopy H) (C.retainedDiskCopy_continuous H)
      (C.double_locus_eq_original_retained H old hdouble), ?_⟩
  intro a ha b hb d hd hab had hnab hnad
  apply Annuli.retained_relation_unique_other_point hKS (C.retainedDiskCopy H)
    (C.retainedDiskCopy_injective H) (C.retained_fiber_relation H hval hdouble)
    ?_ a b d ha hb hd hab had hnab hnad
  intro a ha b hb d hd hab had hnab hnad
  let x : doubleLocusOn old S := ⟨a, ha, b, hb, hab, hnab⟩
  exact (hunique x b hb hab hnab).trans (hunique x d hd had hnad).symm

end PoincareConjecture.M76.Dehn.AnnulusSquareCopies
