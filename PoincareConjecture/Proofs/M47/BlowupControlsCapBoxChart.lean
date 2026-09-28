import PoincareConjecture.Proofs.M47.BlowupControlsCapBoxMetric
import PoincareConjecture.Proofs.M44.Mathlib.SmoothImageInverse










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

open M36

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}


def capBoxDomain (N : EpsilonNeck g) (s : ℝ) : Set E :=
  centeredNeckDomain N s ∩ {p | ‖cylinderHorizontalProjection p‖ < 1}

theorem capBoxDomain_isOpen (N : EpsilonNeck g) (s : ℝ) :
    IsOpen (capBoxDomain N s) :=
  (centeredNeckDomain_isOpen N s).inter
    (isOpen_lt cylinderHorizontalProjection.continuous.norm continuous_const)

private theorem capBoxImage_isOpen (N : EpsilonNeck g) (q : UnitTwoSphere) (s : ℝ) :
    IsOpen (centeredNeckLift N q s '' capBoxDomain N s) := by
  apply Poincare.isOpen_image_of_smooth_leftInvOn (inverse := centeredNeckInverse N q s)
    (capBoxDomain_isOpen N s)
    (fun p hp => (centeredNeckLift_contMDiffAt N q s hp.1).contMDiffWithinAt)
  · rintro y ⟨p, hp, rfl⟩
    exact (centeredNeckInverse_contMDiffAt_lift N q s hp.1).contMDiffWithinAt
  · intro p hp
    exact centeredNeckInverse_lift N q s hp.1


noncomputable def capBoxChart (N : EpsilonNeck g) (q : UnitTwoSphere) (s : ℝ) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞ where
  toFun := centeredNeckLift N q s
  invFun := centeredNeckInverse N q s
  source := capBoxDomain N s
  target := centeredNeckLift N q s '' capBoxDomain N s
  map_source' p hp := ⟨p, hp, rfl⟩
  map_target' := by
    rintro y ⟨p, hp, rfl⟩
    rwa [centeredNeckInverse_lift N q s hp.1]
  left_inv' p hp := centeredNeckInverse_lift N q s hp.1
  right_inv' := by
    rintro y ⟨p, hp, rfl⟩
    rw [centeredNeckInverse_lift N q s hp.1]
  open_source := capBoxDomain_isOpen N s
  open_target := capBoxImage_isOpen N q s
  contMDiffOn_toFun p hp := (centeredNeckLift_contMDiffAt N q s hp.1).contMDiffWithinAt
  contMDiffOn_invFun := by
    rintro y ⟨p, hp, rfl⟩
    exact (centeredNeckInverse_contMDiffAt_lift N q s hp.1).contMDiffWithinAt



theorem capBoxChart_inverse_tangent_bound (N : EpsilonNeck g) (q : UnitTwoSphere)
    (s : ℝ) {p : E} (hp : p ∈ (capBoxChart N q s).source) (v : E) :
    ‖v‖ ≤ (2 / N.scale) * g.tangentNorm (capBoxChart N q s p)
      (mfderiv (𝓡 3) (𝓡 3) (capBoxChart N q s) p v) := by
  have hscale := N.scale_pos
  have hlo := (cap_box_neck_tangent_bounds N q s hp.1 hp.2.le v).1
  change ‖v‖ ≤ (2 / N.scale) * g.tangentNorm (centeredNeckLift N q s p)
    (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N q s) p v)
  have h := mul_le_mul_of_nonneg_left hlo (by positivity : 0 ≤ 2 / N.scale)
  have hcancel : (2 / N.scale) * (N.scale / 2 * ‖v‖) = ‖v‖ := by
    field_simp [N.scale_pos.ne']
  rwa [hcancel] at h

end PoincareConjecture.M47
