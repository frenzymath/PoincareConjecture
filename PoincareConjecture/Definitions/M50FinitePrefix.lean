import PoincareConjecture.Definitions.M49VolumeLoss










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure RepairedFinitePrefixData
    (F : SurgeryFlowData.{u})
    (C : RepairedVolumeLossControls F)
    (V : RepairedVolumeLossData F C) where

  volume_loss : RepairedVolumeLossData F C
  volume_loss_eq : volume_loss = V

  local_finite : ∀ Kset : Set ℝ, IsCompact Kset →
    (F.surgery_times ∩ Kset).Finite

  no_finite_accumulation : ∀ T : ℝ,
    ∃ d : ℝ, 0 < d ∧
      (F.surgery_times ∩ Set.Ioo (T - d) (T + d)).Finite

end PoincareConjecture
