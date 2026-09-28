import PoincareConjecture.Proofs.M47.BlowupControlsCapNeckRealization
import PoincareConjecture.Proofs.M47.BlowupControlsCapAxialNormalizedClose
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckLocality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

open Proofs.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "V" => RoundCylinderCoordinates
local notation "Ic" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem cap_neck_affine_pullback (N : EpsilonNeck g) (lambda c : ℝ)
    {z : RoundCylinderSpace}
    (hz : lambda * z.2 + c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v w : RoundCylinderTangent z) :
    roundCylinderPullback g (N.coordinate_map ∘ neckAxialSpaceMap lambda c) z v w =
      neckAxialTensorPullback lambda c (roundCylinderPullback g N.coordinate_map) z v w := by
  have hN := (N.coordinate_map_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds
      (show neckAxialSpaceMap lambda c z ∈ univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ from
        ⟨mem_univ _, hz⟩))).mdifferentiableAt (by simp)
  have hA : MDifferentiableAt Ic Ic (neckAxialSpaceMap lambda c) z :=
    (neckAxialSpaceMap_contMDiff lambda c).contMDiffAt.mdifferentiableAt (by simp)
  unfold roundCylinderPullback neckAxialTensorPullback
  rw [mfderiv_comp z hN hA]
  simp only [ContinuousLinearMap.comp_apply, neckAxialSpaceMap_mfderiv, Function.comp_apply]

theorem cap_neck_affine_normalized_comparison (N : EpsilonNeck g)
    (hsmall : N.epsilon ≤ 1 / 1200)
    {epsilon lambda c : ℝ} (hepsilon : 0 < epsilon)
    (haccuracy : 6 * N.epsilon ≤ epsilon) (q : UnitTwoSphere)
    (hc : c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hlambda : 0 ≤ lambda)
    (hscale : (N.scale ^ 2 * N.connection.scalarCurvature (N.coordinate_map (q, c))) *
      lambda ^ 2 = 1)
    (hdomain : ∀ s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹,
      lambda * s + c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    RoundCylinderClose epsilon 0 (fun z v w =>
      N.connection.scalarCurvature (N.coordinate_map (q, c)) *
        roundCylinderPullback g (N.coordinate_map ∘ neckAxialSpaceMap lambda c) z v w) := by
  let beta := N.scale ^ 2 * N.connection.scalarCurvature (N.coordinate_map (q, c))
  let B : RoundCylinderSpace → V →L[ℝ] V →L[ℝ] ℝ := fun z =>
    let G : E →L[ℝ] E →L[ℝ] ℝ := g.inner (N.coordinate_map z)
    let L : V →L[ℝ] E := mfderiv Ic (𝓡 3) N.coordinate_map z
    N.scale⁻¹ ^ 2 • G.bilinearComp L L
  obtain ⟨g1, D1, U, hU, hpU, hcoeff, hscalar⟩ :=
    cap_neck_normalized_metric_realization N q hc
  have hclose := cap_native_axial_normalized_close N.epsilon_pos hsmall hepsilon haccuracy
    B N.metric_comparison.close g1 D1 q hU hcoeff c hc hpU hscalar.symm hlambda hscale hdomain
  have heq (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
      (v w : RoundCylinderTangent z) :
      beta * neckAxialTensorPullback lambda c (fun z v w => B z v w) z v w =
        N.connection.scalarCurvature (N.coordinate_map (q, c)) *
          roundCylinderPullback g (N.coordinate_map ∘ neckAxialSpaceMap lambda c) z v w := by
    rw [cap_neck_affine_pullback N lambda c (hdomain z.2 hz)]
    change (N.scale ^ 2 * N.connection.scalarCurvature (N.coordinate_map (q, c))) *
      (N.scale⁻¹ ^ 2 * _) = _
    field_simp [N.scale_pos.ne']
    rfl
  refine ⟨hclose.1.congr_cylinder heq, ?_⟩
  obtain ⟨bound, hbound, hjet⟩ := hclose.2
  refine ⟨bound, hbound, fun z hz => ?_⟩
  rw [← M34.roundCylinderJetErrorSquared_eq_of_eqOn_cylinder heq 0 _ hz]
  exact hjet z hz

end PoincareConjecture.M47
