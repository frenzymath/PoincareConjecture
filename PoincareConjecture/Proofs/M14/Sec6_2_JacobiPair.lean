import PoincareConjecture.Proofs.M14.Sec6_2_PullbackRestriction
import PoincareConjecture.Proofs.M14.Sec6_2_PullbackCongruence
import PoincareConjecture.Proofs.M14.Sec6_2_PullbackMetric

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

theorem pullbackExtension_field_contMDiffOn {γ : ℝ → G.Point} {J : Set ℝ}
    {Y : ∀ s, G.Horizontal (γ s)} (E : M14PullbackExtension G γ J Y)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ γ J) :
    ContMDiffOn (𝓘(ℝ, ℝ)) ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (γ s) (Y s)) J := by
  obtain ⟨U, hU, hgraph, hE⟩ := E.joint_smooth
  have h := hE.comp (contMDiffOn_id.prodMk hγ) hgraph
  apply h.congr
  intro s hs
  dsimp only [Function.comp_def, id_eq]
  rw [E.agrees s hs]

variable {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  (R : M14SquareRootPath G p)

noncomputable def horizontalJacobiPairResidual (s : ℝ)
    (Y P DP W : G.Horizontal (R.curve s)) : ℝ :=
  let q := R.curve s
  let A := M14SquareRootVelocity R s
  G.spacetime.horizontalMetric.inner q DP W +
    horizontalRiemann G.leafwise q Y A W A -
    2 * s * M14BcalPairing G q A Y W -
    2 * s ^ 2 * M14HorizontalHessianPairing G q Y W +
    4 * s * M14HorizontalRicciDerivativePairing G q Y A W +
    4 * s * horizontalRicci G.leafwise q P W

structure IsHorizontalJacobiPairOn (a b : ℝ)
    (z : ∀ s, G.Horizontal (R.curve s) × G.Horizontal (R.curve s)) : Prop where
  ordered : a < b
  interval_subset : Icc a b ⊆ M14SqrtParameterInterval τ₁ τ₂
  first_smooth : ContMDiffOn (𝓘(ℝ, ℝ))
    ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
    (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (R.curve s) (z s).1) (Icc a b)
  second_smooth : ContMDiffOn (𝓘(ℝ, ℝ))
    ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
    (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (R.curve s) (z s).2) (Icc a b)
  equations : ∃ EY : M14PullbackExtension G R.curve (Icc a b) (fun s => (z s).1),
    ∃ EP : M14PullbackExtension G R.curve (Icc a b) (fun s => (z s).2),
      (∀ s ∈ Icc a b, M14HorizontalCovariantDerivative G R.curve (Icc a b)
        (fun r => (z r).1) EY s = (z s).2) ∧
      ∀ s ∈ Icc a b, ∀ W : G.Horizontal (R.curve s),
        horizontalJacobiPairResidual R s (z s).1 (z s).2
          (M14HorizontalCovariantDerivative G R.curve (Icc a b) (fun r => (z r).2) EP s) W = 0

variable {R} {a b : ℝ}
  {z w : ∀ s, G.Horizontal (R.curve s) × G.Horizontal (R.curve s)}

theorem IsHorizontalJacobiPairOn.congr (h : IsHorizontalJacobiPairOn R a b z)
    (hzw : ∀ s ∈ Icc a b, z s = w s) : IsHorizontalJacobiPairOn R a b w := by
  obtain ⟨EY, EP, hY, hP⟩ := h.equations
  have hfirst := fun s hs => congrArg Prod.fst (hzw s hs)
  have hsecond := fun s hs => congrArg Prod.snd (hzw s hs)
  let EY' := pullbackExtensionCongr EY rfl (fun s hs => heq_of_eq (hfirst s hs))
  let EP' := pullbackExtensionCongr EP rfl (fun s hs => heq_of_eq (hsecond s hs))
  refine ⟨h.ordered, h.interval_subset, ?_, ?_, EY', EP', ?_, ?_⟩
  · exact h.first_smooth.congr (fun s hs => by rw [← hzw s hs])
  · exact h.second_smooth.congr (fun s hs => by rw [← hzw s hs])
  · intro s hs
    exact (hY s hs).trans (hsecond s hs)
  · intro s hs W
    change horizontalJacobiPairResidual R s (w s).1 (w s).2
      (M14HorizontalCovariantDerivative G R.curve (Icc a b) (fun r => (z r).2) EP s) W = 0
    rw [← hzw s hs]
    exact hP s hs W

theorem IsHorizontalJacobiPairOn.equations_for_extensions
    (h : IsHorizontalJacobiPairOn R a b z)
    (EY : M14PullbackExtension G R.curve (Icc a b) (fun s => (z s).1))
    (EP : M14PullbackExtension G R.curve (Icc a b) (fun s => (z s).2)) :
    (∀ s ∈ Icc a b, M14HorizontalCovariantDerivative G R.curve (Icc a b)
      (fun r => (z r).1) EY s = (z s).2) ∧
    ∀ s ∈ Icc a b, ∀ W : G.Horizontal (R.curve s),
      horizontalJacobiPairResidual R s (z s).1 (z s).2
        (M14HorizontalCovariantDerivative G R.curve (Icc a b) (fun r => (z r).2) EP s) W = 0 := by
  obtain ⟨EY₀, EP₀, hY, hP⟩ := h.equations
  have hR := R.smooth.mono (h.interval_subset.trans R.interval_subset)
  constructor
  · intro s hs
    rw [← horizontalCovariantDerivative_extension_independent EY₀ EY hs
      (uniqueDiffOn_Icc h.ordered s hs) ((hR s hs).mdifferentiableWithinAt (by simp))]
    exact hY s hs
  · intro s hs W
    rw [← horizontalCovariantDerivative_extension_independent EP₀ EP hs
      (uniqueDiffOn_Icc h.ordered s hs) ((hR s hs).mdifferentiableWithinAt (by simp))]
    exact hP s hs W

theorem IsHorizontalJacobiPairOn.restrict (h : IsHorizontalJacobiPairOn R a b z)
    {c d : ℝ} (hac : a ≤ c) (hcd : c < d) (hdb : d ≤ b) :
    IsHorizontalJacobiPairOn R c d z := by
  have hsub : Icc c d ⊆ Icc a b := Icc_subset_Icc hac hdb
  have hR := R.smooth.mono (h.interval_subset.trans R.interval_subset)
  obtain ⟨EY, EP, hY, hP⟩ := h.equations
  refine ⟨hcd, hsub.trans h.interval_subset, h.first_smooth.mono hsub,
    h.second_smooth.mono hsub, pullbackExtensionRestrict EY hsub,
    pullbackExtensionRestrict EP hsub, ?_, ?_⟩
  · intro s hs
    rw [← horizontalCovariantDerivative_restrict_subset EY hsub
      (uniqueDiffOn_Icc hcd s hs) ((hR s (hsub hs)).mdifferentiableWithinAt (by simp))]
    exact hY s (hsub hs)
  · intro s hs W
    rw [← horizontalCovariantDerivative_restrict_subset EP hsub
      (uniqueDiffOn_Icc hcd s hs) ((hR s (hsub hs)).mdifferentiableWithinAt (by simp))]
    exact hP s (hsub hs) W

end PoincareConjecture.M14
