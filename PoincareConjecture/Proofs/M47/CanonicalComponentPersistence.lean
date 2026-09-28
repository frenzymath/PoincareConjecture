import PoincareConjecture.Proofs.M47.CanonicalComponentSectionalStability
import PoincareConjecture.Proofs.M47.CanonicalComponentDiameterStability

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M] [CompactSpace M]

theorem eventually_same_C_component
    (hC : RicciFlowCurvatureTheory.{u}) {a b : ℝ} (F : RicciFlow 3 M (Icc a b))
    (t : Icc a b) {C : ℝ}
    (N : SingularCComponent (F.metric t.val) (F.connection t.val) C) :
    ∀ᶠ s : Icc a b in 𝓝 t,
      ∃ N' : SingularCComponent (F.metric s.val) (F.connection s.val) C,
        N'.carrier = N.carrier ∧ N'.basepoint = N.basepoint := by
  filter_upwards [component_sectional_bounds_persist hC F t N,
    component_diameter_bounds_persist hC F t N] with s hsectional hdiameter
  exact ⟨{
    constant_pos := N.constant_pos
    basepoint := N.basepoint
    carrier := N.carrier
    component_eq := N.component_eq
    compact := N.compact
    topology := N.topology
    positive_sectional := hsectional.1
    sectional_lower := hsectional.2
    diameter_lower := hdiameter.1
    diameter_upper := hdiameter.2 }, rfl, rfl⟩

end PoincareConjecture.Proofs.M47
