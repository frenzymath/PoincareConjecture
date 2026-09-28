import PoincareConjecture.Proofs.M76.Mathlib.ClosedComplementHeightSigns
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLHomeomorph

set_option autoImplicit false

open Set

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem mem_both_height_closures_of_ordinary_terminal_bands
    {S s s' T : Set E} (A : E →ᵃ[ℝ] ℝ) {t β : ℝ}
    (hs' : IsClosed s') (hunion : s ∪ s' = S)
    (hcut : s ∩ s' ⊆ {x | A x = 0}) (ht : 0 < t)
    (hterminal : ∀ a b : ℝ, t < a → b ≤ β →
      ∃ G : (s ∩ {x | A x ∈ Icc a b} : Set E) ≃ₜ
          (T ∩ {x | A x ∈ Icc a b} : Set E),
        G.IsFinitePL ∧ ∀ x, A (G x) = A x)
    (hsource : ∀ x ∈ S, A x ∈ Ioo (0 : ℝ) β →
      x ∈ closure (S ∩ {y | A y < A x}) ∧
        x ∈ closure (S ∩ {y | A x < A y})) :
    ∀ x ∈ T, A x ∈ Ioo t β →
      x ∈ closure (T ∩ {y | A y < A x}) ∧
        x ∈ closure (T ∩ {y | A x < A y}) := by
  intro x hx hxA
  obtain ⟨a, hta, hac⟩ := exists_between hxA.1
  obtain ⟨b, hcb, hbβ⟩ := exists_between hxA.2
  obtain ⟨G, _, hGA⟩ := hterminal a b hta hbβ.le
  let Z := s' ∩ {y | A y ∈ Icc a b}
  have hZ : IsClosed Z := hs'.inter (isClosed_Icc.preimage A.continuous_of_finiteDimensional)
  have hcover : ((s ∩ {y | A y ∈ Icc a b}) ∩ {y | A y ∈ Icc a b}) ∪ Z =
      S ∩ {y | A y ∈ Icc a b} := by
    ext y
    constructor
    · rintro (⟨⟨hys, hyA⟩, _⟩ | ⟨hys', hyA⟩)
      · exact ⟨hunion.subset (Or.inl hys), hyA⟩
      · exact ⟨hunion.subset (Or.inr hys'), hyA⟩
    · intro hy
      rcases hunion.symm.subset hy.1 with hys | hys'
      · exact Or.inl ⟨⟨hys, hy.2⟩, hy.2⟩
      · exact Or.inr ⟨hys', hy.2⟩
  let y := G.symm ⟨x, ⟨hx, ⟨hac.le, hcb.le⟩⟩⟩
  have hGy : (G y : E) = x := congrArg Subtype.val (G.apply_symm_apply _)
  have hyA : A y = A x := (hGA y).symm.trans (congrArg A hGy)
  have hypos : 0 < A y := hyA.symm ▸ ht.trans hxA.1
  have hyZ : (y : E) ∉ Z := fun hy => hypos.ne' (hcut ⟨y.property.1, hy.1⟩)
  obtain ⟨hlo, hhi⟩ := hsource y (hunion.subset (Or.inl y.property.1))
    ⟨hypos, hyA.symm ▸ hxA.2⟩
  have hsigns := G.mem_both_height_closures_of_closed_band_cover A A
    A.continuous_of_finiteDimensional hGA hZ hcover y hyZ
      (hyA.symm ▸ hac) (hyA.symm ▸ hcb) hlo hhi
  rw [hGy] at hsigns
  exact ⟨closure_mono (inter_subset_inter_left _ inter_subset_left) hsigns.1,
    closure_mono (inter_subset_inter_left _ inter_subset_left) hsigns.2⟩

end Homeomorph
