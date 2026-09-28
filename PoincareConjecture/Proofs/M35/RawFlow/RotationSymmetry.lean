import PoincareConjecture.Proofs.M35.Uniqueness.RotationGeneration
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Exhaustion.RegularRotationHeat

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.RawFlow

open Uniqueness Uniqueness.Heat

theorem rotation_invariant_of_compact_heat
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) {T : ℝ} (hT : 0 < T) (hTlt : T < G.lifetime)
    (h01 : ∀ E : Set StandardCapSpace, IsCompact E → Nonempty
      (CompactKillingHeat G T (4 * ‖coordinateRotationGenerator‖ ^ 2)
        (9 * ‖coordinateRotationGenerator‖ ^ 2) (fun y => coordinateRotationGenerator y) E))
    (h02 : ∀ E : Set StandardCapSpace, IsCompact E → Nonempty
      (CompactKillingHeat G T (4 * ‖coordinateRotation02Generator‖ ^ 2)
        (9 * ‖coordinateRotation02Generator‖ ^ 2) (fun y => coordinateRotation02Generator y) E)) :
    ∀ t ∈ Icc 0 T, ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        (G.flow.metric t).inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) =
            (G.flow.metric t).inner x u v := by
  have hk01 := raw_killing_of_compact_heat P G hT hTlt (by positivity) (by positivity)
    coordinateRotationGenerator.contDiff h01
  have hk02 := raw_killing_of_compact_heat P G hT hTlt (by positivity) (by positivity)
    coordinateRotation02Generator.contDiff h02
  exact fun t ht => rotation_invariant_of_coordinate_killing (G.flow.connection t)
    (hk01 t ht) (hk02 t ht)

end PoincareConjecture.M35.RawFlow
