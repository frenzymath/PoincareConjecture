import PoincareConjecture.Statements.M32HornSelection
import PoincareConjecture.Proofs.M32.Thm11_31.UniformHeight
import PoincareConjecture.Proofs.M32.Cor11_36.Downward













set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture












































theorem m32HornSelection
    (P : RepairedHornSelectionPredecessors.{u}) :
    RepairedHornSelectionTheory.{u} := by
  obtain ⟨epsilonDeep, hDeepPos, hDeepSmall, hdeep⟩ := M32.exists_uniform_deepHornHeight P
  obtain ⟨tauDownward, hDownPos, _hDownSmall, hselector⟩ :=
    M32.exists_deepHornScaleSelection_of_pointwiseHeight.{u}
  refine {
    providers := P
    deep_horn := ⟨epsilonDeep, hDeepPos, hDeepSmall, ?_⟩
    scale_selection := ?_
    selection := ?_ }
  · intro epsilon hepsilon hsmall r₀ C analyticConstant rho delta
      hr₀ hC hAnalytic hrho hrhor₀ hdelta A hA
    obtain ⟨h, hh, hheight⟩ := hdeep epsilon hepsilon hsmall
      r₀ C analyticConstant rho delta hr₀ hC hAnalytic hrho hrhor₀ hdelta A hA
    exact ⟨h, hh, hheight.1, hheight.2⟩
  · let epsilonSelector := min epsilonDeep (tauDownward / terminalAccuracyFactor)
    have hSelectorPos : 0 < epsilonSelector :=
      lt_min hDeepPos (div_pos hDownPos terminalAccuracyFactor_pos)
    refine ⟨epsilonSelector, hSelectorPos, (min_le_left _ _).trans hDeepSmall, ?_⟩
    intro epsilon C analyticConstant hepsilon hsmall hC hAnalytic A hA
    have hDeep : epsilon ≤ epsilonDeep := hsmall.trans (min_le_left _ _)
    have hDown : terminalAccuracyFactor * epsilon ≤ tauDownward :=
      (le_div_iff₀' terminalAccuracyFactor_pos).mp (hsmall.trans (min_le_right _ _))
    apply hselector epsilon C analyticConstant hDown hC
    intro r₀ rho delta hr₀ hrho hrhor₀ hdelta
    exact hdeep epsilon hepsilon hDeep r₀ C analyticConstant rho delta
      hr₀ hC hAnalytic hrho hrhor₀ hdelta A hA
  · intro L31 M _ _ _ _ _ _ _ _ F T H A hsmall _hA
    obtain ⟨Q⟩ := (Classical.choose_spec (L31.limit A)).2.2 H hsmall
    exact ⟨{ limit := Q }⟩

end PoincareConjecture
