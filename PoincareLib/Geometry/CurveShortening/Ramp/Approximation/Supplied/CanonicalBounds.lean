import PoincareLib.Geometry.CurveShortening.Ramp.Approximation.Raw.LoopLength
import PoincareLib.Geometry.CurveShortening.Ramp.Approximation.Polygon.Estimates

/-!
# Canonical bounds for the exact supplied approximation

Nonnegative length loss and the actual polygon bound apply to the same
supplied raw approximation, without restricting its tolerance. Lemma 19.17
and Claim 19.22, MT2007 pp. 449-453; see
`2026-09-21-family-length-and-canonical-bounds.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

namespace PoincareMT

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}
  {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))}
  {zeta circumference : ℝ}

/-- The canonical graph of the supplied approximation is bounded by the
actual source length supremum plus its circumference. The length-loss
sign suffices for every tolerance. Lemma 19.17, MT2007 pp. 449-453. -/
theorem M63RawApproximation.canonical_length_le (A : M63RawApproximation F Gamma zeta)
    (P : M62.CircleProductData F circumference) (z : LoopTwoSphere) :
    m62Length P.flow (fun x _ => m63CanonicalRamp P (periodicFreeLoop (A.family z)) x) a ≤
      m63FamilyLengthSup (F.metric a) Gamma + circumference := by
  have hlength : freeLoopLength (F.metric a) (A.family z) ≤
      freeLoopLength (F.metric a) (Gamma z) := sub_nonneg.mp (A.length_loss z).1
  have hsup := (m63FamilyLengthSup_properties (F.metric a) Gamma).2.2.2 z
  apply (M63.canonicalRamp_length_le P ((A.angular_smooth z).of_le (by simp)) a).trans
  change freeLoopLength (F.metric a) (A.family z) + circumference ≤ _
  exact add_le_add (hlength.trans hsup) le_rfl

/-- The supplied approximation's canonical graph has the bound for its
exact polygon count. Angular equality transfers actual curvature and
speed together. Claim 19.22, MT2007 pp. 452-453. -/
theorem M63RawApproximation.canonical_totalCurvature_le
    (A : M63RawApproximation F Gamma zeta) (P : M62.CircleProductData F circumference)
    (z : LoopTwoSphere) :
    m62TotalCurvature P.flow
      (fun x _ => m63CanonicalRamp P (periodicFreeLoop (A.family z)) x) a ≤
        (A.count : ℝ) * Real.pi := by
  have heq : periodicFreeLoop (A.family z) = m63FlattenedPolygon (A.polygon z) :=
    funext (A.angular_eq z)
  rw [heq]
  exact m63FlattenedPolygon_graph_totalCurvature P a (A.polygon z) A.count_positive

end PoincareMT
