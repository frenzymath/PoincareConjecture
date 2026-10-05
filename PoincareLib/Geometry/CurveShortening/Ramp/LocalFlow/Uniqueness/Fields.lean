import PoincareLib.Geometry.CurveShortening.Ramp.LocalFlow.Uniqueness.Closed
import PoincareLib.Geometry.CurveShortening.Ramp.Analysis.Compact.EmbeddedRetraction
import Mathlib.Geometry.Manifold.WhitneyEmbedding

/-!
# Actual compact closed and half-open uniqueness

The compact ambient manifold supplies its own smooth embedding and
retraction. Actual fixed-label closed uniqueness then gives the two
frozen uniqueness fields without an existence premise. MT2007
Claim 19.1, p. 437;
`2026-09-22-uniqueness-compact-field-adapters.md`.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

/-- Any two actual C2 normal solutions in the compact ambient manifold
with equal initial labels agree on their full closed time interval.
MT2007 Claim 19.1, p. 437; compact uniqueness adapters, statement 1.
The interval may be empty or a singleton. -/
theorem c2ShrinkingCurve_unique_closed (F : RicciFlow n M (Icc a b))
    (hcompact : IsCompact (univ : Set M))
    {s T : ℝ} {c d : ℝ → ℝ → M}
    (hc : M63C2ShrinkingCurveOn F c (Icc s T))
    (hd : M63C2ShrinkingCurveOn F d (Icc s T))
    (hinit : ∀ x, c x s = d x s) :
    ∀ t ∈ Icc s T, ∀ x, c x t = d x t := by
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  let : Nonempty M := ⟨c 0 s⟩
  obtain ⟨N, e, he, hemb, hinj⟩ := exists_embedding_euclidean_of_compact (I := 𝓡 n) (M := M)
  obtain ⟨U, ρ, hU, heU, hρ, hρe, _hmin, _huniq⟩ :=
    exists_smooth_compact_embedded_retraction e hemb he hinj
  exact c2ShrinkingCurve_unique_closed_of_retraction he hU heU hρ hρe hc hd hinit

/-- The actual compact closed theorem supplies uniqueness at every
included half-open time by restriction to a shorter closed interval.
MT2007 Claim 19.1, p. 437; compact uniqueness adapters, statement 2.
No trace or time derivative is asserted at the omitted endpoint. -/
theorem c2ShrinkingCurve_unique_half_open (F : RicciFlow n M (Icc a b))
    (hcompact : IsCompact (univ : Set M))
    {T : ℝ} (haT : a < T) (hTb : T ≤ b)
    {c d : ℝ → ℝ → M}
    (hc : M63C2ShrinkingCurveOn F c (Ico a T))
    (hd : M63C2ShrinkingCurveOn F d (Ico a T))
    (hinit : ∀ x, c x a = d x a) :
    ∀ t ∈ Ico a T, ∀ x, c x t = d x t := by
  exact unique_half_open_of_unique_closed
    (fun _ _ _ _ _ hc hd hinit => c2ShrinkingCurve_unique_closed F hcompact hc hd hinit)
    haT hTb hc hd hinit

end PoincareMT.M63
