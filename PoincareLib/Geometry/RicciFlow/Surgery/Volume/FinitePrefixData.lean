import PoincareLib.Geometry.RicciFlow.Surgery.Volume.LossData

/-!
Adapted from Mapher `PoincareMT/Definitions/M50FinitePrefix.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M50 repaired finite-prefix flow data

This package records the finite-horizon event bound supplied by M49 and its
compact-set and no-accumulation consequences for the same actual flow.
Finite epoch continuation is owned by M48; it is not an additional universal
service hidden in this volume-loss consequence.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

structure RepairedFinitePrefixData
    (F : SurgeryFlowData.{u})
    (C : RepairedVolumeLossControls F)
    (V : RepairedVolumeLossData F C) where
  /-- The concrete M49 certificate is retained, rather than a phantom index. -/
  volume_loss : RepairedVolumeLossData F C
  volume_loss_eq : volume_loss = V
  /-- Compact-set finiteness is the source-facing form of the M49 bound. -/
  local_finite : ∀ Kset : Set ℝ, IsCompact Kset →
    (F.surgery_times ∩ Kset).Finite
  /-- This is the finite-horizon consequence, stated for every finite center. -/
  no_finite_accumulation : ∀ T : ℝ,
    ∃ d : ℝ, 0 < d ∧
      (F.surgery_times ∩ Set.Ioo (T - d) (T + d)).Finite

end PoincareMT
