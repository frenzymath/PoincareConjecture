import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.RawLoopLength
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.PolygonEstimates

set_option autoImplicit false

open scoped Manifold ContDiff

namespace PoincareConjecture

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}
  {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))}
  {zeta circumference : ℝ}

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

end PoincareConjecture
