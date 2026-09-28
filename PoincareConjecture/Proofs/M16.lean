import PoincareConjecture.Statements.M16StructuralKappa
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Structure








set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture
























theorem ancientKappaStructuralConsequences
    (n : ℕ)
    (hM04 : RicciFlowCurvatureTheory.{u})
    (hM06 : HarnackAncientTheory.{u})
    (hM13 : GeneralizedParabolicRescalingTheory.{u} n) :
    AncientKappaStructuralConclusion.{u} n := by
  exact horizon_ancientKappaStructuralConsequences n hM04 hM06 hM13

end PoincareConjecture
