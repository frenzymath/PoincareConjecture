import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Step.OtherLevels

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SphereSurgeryStep

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 -> E3} {v : E3} {c R : Real} (S : SphereSurgeryStep f v c R)

def capMinusHeights : Set Real :=
  (fun x : E2 => inner Real v (S.gMinus x)) '' closedBall 0 1

def capPlusHeights : Set Real :=
  (fun x : E2 => inner Real v (S.gPlus x)) '' closedBall 0 1

theorem isCompact_capMinusHeights : IsCompact S.capMinusHeights :=
  (isCompact_closedBall (0 : E2) 1).image
    ((innerSL Real v).continuous.comp S.gMinus_smooth.continuous)

theorem isCompact_capPlusHeights : IsCompact S.capPlusHeights :=
  (isCompact_closedBall (0 : E2) 1).image
    ((innerSL Real v).continuous.comp S.gPlus_smooth.continuous)

theorem disjoint_cuts_capMinusHeights {A : Set Real}
    (hsep : ∀ k ∈ A, k ≠ c -> R < |k - c|) : Disjoint A S.capMinusHeights := by
  apply Set.disjoint_left.mpr
  rintro k hk ⟨x, _, hx⟩
  by_cases hkc : k = c
  · exact S.capMinus_avoids x (hx.trans hkc)
  · exact S.capMinus_avoids_of_far (hsep k hk hkc) x hx

theorem disjoint_cuts_capPlusHeights {A : Set Real}
    (hsep : ∀ k ∈ A, k ≠ c -> R < |k - c|) : Disjoint A S.capPlusHeights := by
  apply Set.disjoint_left.mpr
  rintro k hk ⟨x, _, hx⟩
  by_cases hkc : k = c
  · exact S.capPlus_avoids x (hx.trans hkc)
  · exact S.capPlus_avoids_of_far (hsep k hk hkc) x hx

end Poincare.Manifold.Schoenflies.SphereSurgeryStep

end

end M38Schoenflies
