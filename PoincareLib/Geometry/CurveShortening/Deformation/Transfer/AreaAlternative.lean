import PoincareLib.Geometry.CurveShortening.Deformation.Profile.AreaComparisonProfile

/-!
# Transferring the area alternative from a net node

The arithmetic step in Morgan--Tian Lemma 19.30, printed p. 462:
annulus errors at the two endpoints combine with
Claim 18.26's exact dependence on initial area.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {t₀ t₁ : ℝ} (F : RicciFlow 3 M (Set.Icc t₀ t₁))

/-- Lemma 19.30, p. 462, area branch: endpoint filling-area errors
transfer the node's estimate, with the exact integrating factor. The
geometric annulus estimates must supply the displayed endpoint errors. -/
theorem m65AreaAlternative_transfer {a0 a1 b0 b1 e0 e1 eta t : ℝ}
    (hinitial : |b0 - a0| ≤ e0) (hterminal : a1 ≤ b1 + e1)
    (hnode : b1 ≤ areaComparisonProfile F b0 t + eta) :
    a1 ≤ areaComparisonProfile F a0 t + eta + e1 +
      Real.exp (-(∫ s in t₀..t, flowScalarCurvatureInfimum F s / 2)) * e0 := by
  have hstart : b0 ≤ a0 + e0 := by linarith [le_abs_self (b0 - a0)]
  have hprofile := areaComparisonProfile_mono F t hstart
  dsimp only at hprofile
  rw [areaComparisonProfile_add] at hprofile
  linarith

end PoincareMT
