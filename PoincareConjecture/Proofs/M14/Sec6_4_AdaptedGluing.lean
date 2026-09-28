import PoincareConjecture.Proofs.M14.Sec6_4_UnitAdaptedField
import PoincareConjecture.Proofs.M14.Sec6_2_JacobiGluing










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p}



theorem horizontalUnitAdaptedOn_paste {a l c r : ℝ}
    (hal : a ≤ l) (hlc : l < c) (hcr : c < r)
    {P Q : ∀ s, G.Horizontal (R.curve s)}
    (hP : IsHorizontalUnitAdaptedFieldOn R a c P)
    (hQ : IsHorizontalUnitAdaptedFieldOn R l r Q)
    (heq : ∀ s ∈ Icc l c, P s = Q s) :
    IsHorizontalUnitAdaptedFieldOn R a r (fun s => if s ≤ c then P s else Q s) := by
  let U := fun s => if s ≤ c then P s else Q s
  have har : a < r := (hal.trans_lt hlc).trans hcr
  have hUC : Icc a r ⊆ M14SqrtParameterInterval τ₁ τ₂ := by
    intro s hs
    by_cases hsc : s ≤ c
    · exact hP.interval_subset ⟨hs.1, hsc⟩
    · exact hQ.interval_subset ⟨hlc.le.trans (le_of_not_ge hsc), hs.2⟩
  have hU := horizontalField_paste_contMDiffOn R.curve hlc P Q hP.smooth hQ.smooth heq
  obtain ⟨E⟩ := exists_pullbackExtension_Icc har hU
  have hR := R.smooth.mono (hUC.trans R.interval_subset)
  have hlocal {d e : ℝ} (hde : IsHorizontalUnitAdaptedFieldOn R d e U)
      (hsub : Icc d e ⊆ Icc a r) :
      ∀ s ∈ Icc d e, ∀ W : G.Horizontal (R.curve s),
        G.spacetime.horizontalMetric.inner (R.curve s)
          (M14HorizontalCovariantDerivative G R.curve (Icc a r) U E s) W =
            -(2 * s) * horizontalRicci G.leafwise (R.curve s) (U s) W := by
    intro s hs W
    rw [horizontalCovariantDerivative_restrict_subset E hsub
      (uniqueDiffOn_Icc hde.ordered s hs) ((hR s (hsub hs)).mdifferentiableWithinAt (by simp))]
    exact hde.equation_for_extension (pullbackExtensionRestrict E hsub) s hs W
  have hleft : IsHorizontalUnitAdaptedFieldOn R a c U := hP.congr (by
    intro s hs
    simp only [U, if_pos hs.2])
  have hright : IsHorizontalUnitAdaptedFieldOn R l r U := hQ.congr (by
    intro s hs
    dsimp only [U]
    split_ifs with hsc
    · exact (heq s ⟨hs.1, hsc⟩).symm
    · rfl)
  refine ⟨har, hUC, hU, E, ?_⟩
  intro s hs W
  by_cases hsc : s ≤ c
  · exact hlocal hleft (Icc_subset_Icc le_rfl hcr.le) s ⟨hs.1, hsc⟩ W
  · exact hlocal hright (Icc_subset_Icc hal le_rfl) s
      ⟨hlc.le.trans (le_of_not_ge hsc), hs.2⟩ W



theorem horizontalUnitAdaptedOn_locality (R : M14SquareRootPath G p) :
    DependentIntervalSolutionLocality (IsHorizontalUnitAdaptedFieldOn R) where
  restrict hac hcd hdb h := h.restrict hac hcd hdb
  paste hal hlc hcr hP hQ heq := horizontalUnitAdaptedOn_paste hal hlc hcr hP hQ heq

end PoincareConjecture.M14
