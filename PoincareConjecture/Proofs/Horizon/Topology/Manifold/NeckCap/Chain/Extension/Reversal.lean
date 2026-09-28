import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.ReversalGeometry
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.RoundCylinder.Reflection.Jets
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Reversal











noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.EpsilonNeck

open RoundCylinderReflection

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

private theorem reversed_metric_comparison :
    NeckMetricJetComparison g N.epsilon N.scale (N.coordinate_map ∘ space) := by
  let B : RoundCylinderTwoTensor := fun z v w =>
    N.scale⁻¹ ^ 2 * roundCylinderPullback g N.coordinate_map z v w
  have hB : ∀ (z : RoundCylinderSpace) (a b : ℝ) (v w : RoundCylinderTangent z),
      B z (a • v) (b • w) = a * b * B z v w := by
    intro z a b v w
    simp only [B, roundCylinderPullback, map_smul, smul_apply, smul_eq_mul]
    ring
  have hclose := close_pullback B hB N.metric_comparison.close
  refine ⟨?_⟩
  rw [roundCylinderPullback_comp]
  exact hclose


def reversed : EpsilonNeck g :=
  { N with
    coordinate := (domain N.epsilon).trans N.coordinate
    coordinate_map := N.coordinate_map ∘ space
    coordinate_map_eq := fun z => N.coordinate_map_eq (domain N.epsilon z)
    coordinate_map_smooth := by
      apply N.coordinate_map_smooth.comp contMDiff_space.contMDiffOn
      intro z hz
      exact ⟨mem_univ _, neg_mem_interval hz.2⟩
    coordinate_inverse := space ∘ N.coordinate_inverse
    coordinate_inverse_mem := by
      intro x hx
      exact ⟨mem_univ _, neg_mem_interval (N.coordinate_inverse_mem x hx).2⟩
    coordinate_inverse_left := by
      intro z
      change space (N.coordinate_inverse (N.coordinate (domain N.epsilon z))) = _
      rw [N.coordinate_inverse_left]
      simp [space, domain]
    coordinate_inverse_right := by
      intro x hx
      convert N.coordinate_inverse_right x hx using 1
      simp [Homeomorph.trans_apply, domain, space]
    coordinate_inverse_smooth :=
      contMDiff_space.comp_contMDiffOn N.coordinate_inverse_smooth
    central_sphere_eq := by
      apply N.central_sphere_eq.trans
      apply image_congr
      rintro ⟨q, t⟩ ⟨_, ht⟩
      have ht' : t = 0 := ht
      subst t
      simp [space]
    metric_comparison := N.reversed_metric_comparison }

@[simp] theorem reversed_epsilon : N.reversed.epsilon = N.epsilon := rfl

@[simp] theorem reversed_scale : N.reversed.scale = N.scale := rfl

@[simp] theorem reversed_center : N.reversed.center = N.center := rfl

@[simp] theorem reversed_carrier : N.reversed.carrier = N.carrier := rfl

@[simp] theorem reversed_central_sphere : N.reversed.central_sphere = N.central_sphere := rfl

@[simp] theorem reversed_coordinate_map (z : RoundCylinderSpace) :
    N.reversed.coordinate_map z = N.coordinate_map (z.1, -z.2) := rfl

@[simp] theorem reversed_coordinate_inverse (x : M) :
    N.reversed.coordinate_inverse x = ((N.coordinate_inverse x).1, -(N.coordinate_inverse x).2) :=
  rfl


theorem reversed_sameUpToReversal : N.reversed.SameUpToReversal N := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, -1, Or.inr rfl, ?_⟩
  intro z _
  simp only [reversed_coordinate_map, neg_one_mul]

@[simp] theorem reversed_region (a b : ℝ) : N.reversed.region a b = N.region (-b) (-a) := by
  ext x
  simp only [region, mem_ofPred_eq, reversed_carrier, reversed_coordinate_inverse]
  constructor <;> rintro ⟨hx, h₁, h₂⟩ <;> refine ⟨hx, ?_, ?_⟩ <;> linarith

@[simp] theorem reversed_isSeparating : N.reversed.IsSeparating ↔ N.IsSeparating :=
  N.reversed_sameUpToReversal.isSeparating_iff

@[simp] theorem reversed_isNonseparating : N.reversed.IsNonseparating ↔ N.IsNonseparating :=
  N.reversed_sameUpToReversal.isNonseparating_iff

end PoincareConjecture.EpsilonNeck
