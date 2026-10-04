import PoincareLib.Topology.Manifold.Smoothing.Dehn.Loops.Mathlib.OldResolutionEndPaths
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Loops.Mathlib.MarkedIntervalHomotopy
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Arcs.Mathlib.SquareTwoIntervalNormalization

/-!
# Uniqueness of the prescribed whole end paths

Every point and every path in the end data has a literal prescribed value.
Thus the upper, alternate and original-rim constructions retain exactly the
same end data even when their existence proofs choose witnesses separately.
Exterior interval charts are compared by homotopies in the original mark.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M76.Dehn.PolygonalCrossingResolution

/-- Complete endpoint formulas determine the entire marked end datum. -/
theorem MarkedResolutionEndData.eq
    {X : Type*} [TopologicalSpace X] {Z : Set X} {τ : ((ℝ × ℝ) × ℝ) → X}
    {b : ℝ} {t : unitInterval} (d e : MarkedResolutionEndData Z τ b t) : d = e := by
  rcases d with ⟨z, a, c, l, r, hz, ha, hc, hl, hr,
    ra, rc, rl, rr, U, L, R, hra, hrc, hrl, hrr, hU, hL, hR, _, _, _⟩
  rcases e with ⟨z', a', c', l', r', hz', ha', hc', hl', hr',
    ra', rc', rl', rr', U', L', R', hra', hrc', hrl', hrr', hU', hL', hR', _, _, _⟩
  have ez : z' = z := Subtype.ext (hz'.trans hz.symm)
  have ea : a' = a := Subtype.ext (ha'.trans ha.symm)
  have ec : c' = c := Subtype.ext (hc'.trans hc.symm)
  have el : l' = l := Subtype.ext (hl'.trans hl.symm)
  have er : r' = r := Subtype.ext (hr'.trans hr.symm)
  subst z' a' c' l' r'
  have era : ra = ra' := Path.ext (funext fun s ↦ Subtype.ext ((hra s).trans (hra' s).symm))
  have erc : rc = rc' := Path.ext (funext fun s ↦ Subtype.ext ((hrc s).trans (hrc' s).symm))
  have erl : rl = rl' := Path.ext (funext fun s ↦ Subtype.ext ((hrl s).trans (hrl' s).symm))
  have err : rr = rr' := Path.ext (funext fun s ↦ Subtype.ext ((hrr s).trans (hrr' s).symm))
  have eU : U = U' := Path.ext (funext fun s ↦ Subtype.ext ((hU s).trans (hU' s).symm))
  have eL : L = L' := Path.ext (funext fun s ↦ Subtype.ext ((hL s).trans (hL' s).symm))
  have eR : R = R' := Path.ext (funext fun s ↦ Subtype.ext ((hR s).trans (hR' s).symm))
  subst ra' rc' rl' rr' U' L' R'
  rfl

/-- The old-sheet diagonals also have unique complete parameters. -/
theorem MarkedResolutionOldEndData.eq
    {X : Type*} [TopologicalSpace X] {Z : Set X} {τ : ((ℝ × ℝ) × ℝ) → X}
    {b : ℝ} {t : unitInterval} {d : MarkedResolutionEndData Z τ b t}
    (v w : MarkedResolutionOldEndData d) : v = w := by
  rcases v with ⟨AR, CL, hAR, hCL, _, _⟩
  rcases w with ⟨AR', CL', hAR', hCL', _, _⟩
  have eAR : AR = AR' := Path.ext (funext fun s ↦ Subtype.ext ((hAR s).trans (hAR' s).symm))
  have eCL : CL = CL' := Path.ext (funext fun s ↦ Subtype.ext ((hCL s).trans (hCL' s).symm))
  subst AR' CL'
  rfl

end PoincareMT.M76.Dehn.PolygonalCrossingResolution

namespace PoincareMT.M76.Dehn

/-- Independently chosen ordered charts of the same actual exterior
interval yield homotopic target paths inside the original mark. -/
theorem marked_interval_chart_paths_homotopic
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {W : Set E} {Z : Set X} {a b : E}
    (p q : Icc (0 : ℝ) 1 ≃ₜ W)
    (hp0 : (p (0 : unitInterval) : E) = a) (hp1 : (p (1 : unitInterval) : E) = b)
    (hq0 : (q (0 : unitInterval) : E) = a) (hq1 : (q (1 : unitInterval) : E) = b)
    (f : E → X) (hf : ContinuousOn f W) (hfZ : MapsTo f W Z)
    {x y : Z} (P Q : Path x y)
    (hP : ∀ s, (P s : X) = f (p s)) (hQ : ∀ s, (Q s : X) = f (q s)) :
    P.Homotopic Q :=
  marked_interval_paths_homotopic p f hf hfZ
    ((intervalChartPath p).cast hp0.symm hp1.symm)
    ((intervalChartPath q).cast hq0.symm hq1.symm)
    (fun s ↦ (p s).property) (fun s ↦ (q s).property) P Q hP hQ

end PoincareMT.M76.Dehn
