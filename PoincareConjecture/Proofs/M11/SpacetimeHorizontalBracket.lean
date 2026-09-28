import PoincareConjecture.Proofs.M11.ScalarBracket
import PoincareConjecture.Definitions.M11GeneralizedFlow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Proofs.M11

theorem spacetime_horizontalBracket {n : ℕ} {X : Type*} [TopologicalSpace X]
    {time : X → ℝ} {I : SpacetimeInterval} (F : GeneralizedFlowSpacetime n X time I)
    (U : ∀ p : F.Point, F.Horizontal p) (O : Set F.Point) (hO : IsOpen O)
    (hU : ContMDiffOn (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : F.Point ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := F.Horizontal) p (U p)) O) (p : F.Point) (hp : p ∈ O) :
    mfderiv (spacetimeModel n) 𝓘(ℝ) F.timeFunction p
      (VectorField.mlieBracket (spacetimeModel n)
        (show ∀ q : F.Point, TangentSpace (spacetimeModel n) q from F.timeVector)
        (fun q : F.Point ↦ (U q).val) p) = 0 := by
  let := F.chartedSpace
  let := F.isManifold
  let := F.horizontalTopology
  let := F.horizontalFiberBundle
  let := F.horizontalVectorBundle
  let := F.horizontalSmoothBundle
  apply scalar_mlieBracket_eq_zero F.time_smooth F.timeVector (fun q ↦ (U q).val)
    O hO p hp (F.timeVector_smooth p)
    ((F.horizontal_inclusion_smooth.comp_contMDiffOn hU).contMDiffAt (hO.mem_nhds hp)) 1 0
  · exact fun q _ ↦ F.timeVector_normalized q
  · exact fun q _ ↦ (U q).property

end PoincareConjecture.Proofs.M11
