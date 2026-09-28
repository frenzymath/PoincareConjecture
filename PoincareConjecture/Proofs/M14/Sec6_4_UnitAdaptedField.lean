import PoincareConjecture.Proofs.M14.Sec6_2_JacobiPair

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  (R : M14SquareRootPath G p)

structure IsHorizontalUnitAdaptedFieldOn (a b : ℝ)
    (P : ∀ s, G.Horizontal (R.curve s)) : Prop where
  ordered : a < b
  interval_subset : Icc a b ⊆ M14SqrtParameterInterval τ₁ τ₂
  smooth : ContMDiffOn (𝓘(ℝ, ℝ))
    ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
    (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (R.curve s) (P s)) (Icc a b)
  equation : ∃ E : M14PullbackExtension G R.curve (Icc a b) P,
    ∀ s ∈ Icc a b, ∀ W : G.Horizontal (R.curve s),
      G.spacetime.horizontalMetric.inner (R.curve s)
        (M14HorizontalCovariantDerivative G R.curve (Icc a b) P E s) W =
          -(2 * s) * horizontalRicci G.leafwise (R.curve s) (P s) W

variable {R} {a b : ℝ} {P Q : ∀ s, G.Horizontal (R.curve s)}

theorem IsHorizontalUnitAdaptedFieldOn.congr (h : IsHorizontalUnitAdaptedFieldOn R a b P)
    (heq : ∀ s ∈ Icc a b, P s = Q s) : IsHorizontalUnitAdaptedFieldOn R a b Q := by
  obtain ⟨E, hE⟩ := h.equation
  let E' := pullbackExtensionCongr E rfl (fun s hs => heq_of_eq (heq s hs))
  refine ⟨h.ordered, h.interval_subset, ?_, E', ?_⟩
  · exact h.smooth.congr (fun s hs => by rw [← heq s hs])
  · intro s hs W
    change G.spacetime.horizontalMetric.inner (R.curve s)
      (M14HorizontalCovariantDerivative G R.curve (Icc a b) P E s) W =
        -(2 * s) * horizontalRicci G.leafwise (R.curve s) (Q s) W
    rw [← heq s hs]
    exact hE s hs W

theorem IsHorizontalUnitAdaptedFieldOn.equation_for_extension
    (h : IsHorizontalUnitAdaptedFieldOn R a b P)
    (E : M14PullbackExtension G R.curve (Icc a b) P) :
    ∀ s ∈ Icc a b, ∀ W : G.Horizontal (R.curve s),
      G.spacetime.horizontalMetric.inner (R.curve s)
        (M14HorizontalCovariantDerivative G R.curve (Icc a b) P E s) W =
          -(2 * s) * horizontalRicci G.leafwise (R.curve s) (P s) W := by
  obtain ⟨E₀, hE₀⟩ := h.equation
  have hR := R.smooth.mono (h.interval_subset.trans R.interval_subset)
  intro s hs W
  rw [← horizontalCovariantDerivative_extension_independent E₀ E hs
    (uniqueDiffOn_Icc h.ordered s hs) ((hR s hs).mdifferentiableWithinAt (by simp))]
  exact hE₀ s hs W

theorem IsHorizontalUnitAdaptedFieldOn.restrict
    (h : IsHorizontalUnitAdaptedFieldOn R a b P)
    {c d : ℝ} (hac : a ≤ c) (hcd : c < d) (hdb : d ≤ b) :
    IsHorizontalUnitAdaptedFieldOn R c d P := by
  have hsub : Icc c d ⊆ Icc a b := Icc_subset_Icc hac hdb
  have hR := R.smooth.mono (h.interval_subset.trans R.interval_subset)
  obtain ⟨E, hE⟩ := h.equation
  refine ⟨hcd, hsub.trans h.interval_subset, h.smooth.mono hsub,
    pullbackExtensionRestrict E hsub, ?_⟩
  intro s hs W
  rw [← horizontalCovariantDerivative_restrict_subset E hsub
    (uniqueDiffOn_Icc hcd s hs) ((hR s (hsub hs)).mdifferentiableWithinAt (by simp))]
  exact hE s (hsub hs) W

end PoincareConjecture.M14
