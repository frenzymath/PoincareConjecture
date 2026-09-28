import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CompactClosedStrip
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.InducedOpenImage









set_option autoImplicit false
open Set

local notation "J" => Icc (-1 : ℝ) 1

variable {A X : Type*} [TopologicalSpace A] [CompactSpace A] [TopologicalSpace X]

theorem Topology.IsEmbedding.exists_two_sided_collar_strips {f : A × J → X}
    (hf : Topology.IsEmbedding f) {W : Set X} (hW : IsOpen W)
    (hzero : ∀ a : A, f (a, ⟨0, by norm_num⟩) ∈ W)
    (hWrange : W ⊆ range f) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
      (∀ (a : A) (t : J), |(t : ℝ)| ≤ δ → f (a, t) ∈ W) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ δ →
        IsOpen (f '' {z : A × J | |(z.2 : ℝ)| < ε}) := by
  obtain ⟨δ, hδ, hδsmall, hstrip⟩ :=
    hf.continuous.exists_closed_strip_subset hW hzero
  refine ⟨δ, hδ, hδsmall, hstrip, ?_⟩
  intro ε _ hεδ
  have hopen : IsOpen {z : A × J | |(z.2 : ℝ)| < ε} :=
    isOpen_Iio.preimage (continuous_abs.comp (continuous_subtype_val.comp continuous_snd))
  apply hf.isInducing.isOpen_image_of_subset_open hopen hW _ hWrange
  rintro _ ⟨z, hz, rfl⟩
  exact hstrip z.1 z.2 (le_trans (le_of_lt hz) hεδ)
