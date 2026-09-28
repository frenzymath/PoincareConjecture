import PoincareConjecture.Proofs.M47.BlowupControlsSourceEvolvingError
import PoincareConjecture.Proofs.M47.BlowupControlsSourceRecentFamilyRegion









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M47 M34

local notation "E" => StandardCapSpace
local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "V" => RoundCylinderCoordinates
local notation "Ic" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {F : SurgeryFlowData.{u}} {t : ℝ} {hT : t ∈ F.surgery_times}
  [Nonempty (F.slice t).carrier] {i : Fin (F.event t hT).cap_count} {A : ℝ}
  {S : MaximalStandardCapFlow F.standard_initial} {eta : ℝ}
  {J : Set ℝ} {U : Set (F.slice t).carrier}
  (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
  (initial : SurgeryCapInitialComparison F t hT i A)
  (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
  (hh : 0 < F.parameters.h t) {g : RiemannianMetric 3 E} (N : EpsilonNeck g)
  (s H c : ℝ)
  (hclock : MapsTo (fun u : ℝ => s + u / H) (Icc (-H * s) 0) J)


noncomputable def sourceRecentCapTensor : ℝ → RoundCylinderTwoTensor :=
  fun u => if hu : u ∈ Icc (-H * s) 0 then
    let phi := actualCapSliceChart e initial comparison (s + u / H) (hclock hu)
    let q := (F.parameters.h t)⁻¹ ^ 2
    let g' := m01RescaledMetric (F.metric (t + (s + u / H) / q)) q
      (sq_pos_of_pos (inv_pos.mpr hh))
    fun z v w => H * neckAxialTensorPullback 1 c
      (roundCylinderPullback g' (phi ∘ N.coordinate_map)) z v w
  else fun _ _ _ => 0


theorem sourceRecentCapTensor_smooth {epsilon : ℝ}
    (hsource : N.carrier ⊆ F.standard_initial.metric.ball 0 A)
    (hdom : ∀ r ∈ Ioo (-epsilon⁻¹) epsilon⁻¹,
      r + c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ∀ u ∈ Icc (-H * s) 0, RoundCylinderTensorSmoothOn epsilon
      (sourceRecentCapTensor e initial comparison hh N s H c hclock u) := by
  intro u hu
  let phi := actualCapSliceChart e initial comparison (s + u / H) (hclock hu)
  let q := (F.parameters.h t)⁻¹ ^ 2
  let g' := m01RescaledMetric (F.metric (t + (s + u / H) / q)) q
    (sq_pos_of_pos (inv_pos.mpr hh))
  have hsource' : N.carrier ⊆ phi.source := by
    rw [actualCapSliceChart_source]
    exact hsource
  have hcoord : ContMDiffOn Ic (𝓡 3) ∞ (phi ∘ N.coordinate_map)
      (univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :=
    phi.contMDiffOn_toFun.comp N.coordinate_map_smooth
      (fun _ hz => hsource' (N.coordinate_map_mem_of_axial_mem hz.2))
  let B : RoundCylinderSpace → V →L[ℝ] V →L[ℝ] ℝ := fun z =>
    let D : V →L[ℝ] E₃ := mfderiv Ic (𝓡 3) (phi ∘ N.coordinate_map) z
    let G : E₃ →L[ℝ] E₃ →L[ℝ] ℝ := g'.inner ((phi ∘ N.coordinate_map) z)
    H • G.bilinearComp D D
  have hB : RoundCylinderTensorSmoothOn N.epsilon (fun z v w => B z v w) :=
    (capPersistence_roundCylinderTensorSmoothOn_pullback g' hcoord).const_mul
  simp only [sourceRecentCapTensor, dif_pos hu]
  change RoundCylinderTensorSmoothOn epsilon (neckAxialTensorPullback 1 c (fun z v w => B z v w))
  exact source_recent_translation_smooth hdom B hB


theorem sourceRecentCapTensor_coefficient_error_le {epsilon K : ℝ}
    (hsource : N.carrier ⊆ F.standard_initial.metric.ball 0 A)
    (hdom : ∀ r ∈ Icc (-epsilon⁻¹) epsilon⁻¹,
      r + c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (m : ℕ)
    (herror : ∀ (u : ℝ) (hu : u ∈ Icc (-H * s) 0),
      let phi := actualCapSliceChart e initial comparison (s + u / H) (hclock hu)
      let q := (F.parameters.h t)⁻¹ ^ 2
      let g' := m01RescaledMetric (F.metric (t + (s + u / H) / q)) q
        (sq_pos_of_pos (inv_pos.mpr hh))
      ∀ q0 : UnitTwoSphere, ∀ r ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹,
        ∀ j ≤ m, ∀ a b : Fin 3,
          ‖iteratedFDeriv ℝ j (fun y => H * roundCylinderTensorCoefficient
            (roundCylinderPullback g' (phi ∘ N.coordinate_map)) (chartAt E₂ q0) y a b -
            H * roundCylinderTensorCoefficient
              (roundCylinderPullback (S.metric (s + u / H)) N.coordinate_map)
              (chartAt E₂ q0) y a b) (0, r)‖ ≤ K) :
    ∀ u ∈ Icc (-H * s) 0, ∀ q0 : UnitTwoSphere,
      ∀ r ∈ Icc (-epsilon⁻¹) epsilon⁻¹, ∀ j ≤ m, ∀ a b : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y => roundCylinderTensorCoefficient
          (sourceRecentCapTensor e initial comparison hh N s H c hclock u) (chartAt E₂ q0) y a b -
          H * roundCylinderTensorCoefficient (neckAxialTensorPullback 1 c
            (roundCylinderPullback (S.metric (s + u / H)) N.coordinate_map))
            (chartAt E₂ q0) y a b) (0, r)‖ ≤ K := by
  intro u hu
  let phi := actualCapSliceChart e initial comparison (s + u / H) (hclock hu)
  let q := (F.parameters.h t)⁻¹ ^ 2
  let g' := m01RescaledMetric (F.metric (t + (s + u / H) / q)) q
    (sq_pos_of_pos (inv_pos.mpr hh))
  have hsource' : N.carrier ⊆ phi.source := by
    rw [actualCapSliceChart_source]
    exact hsource
  have hcoord : ContMDiffOn Ic (𝓡 3) ∞ (phi ∘ N.coordinate_map)
      (univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :=
    phi.contMDiffOn_toFun.comp N.coordinate_map_smooth
      (fun _ hz => hsource' (N.coordinate_map_mem_of_axial_mem hz.2))
  let B : RoundCylinderSpace → V →L[ℝ] V →L[ℝ] ℝ := fun z =>
    let D : V →L[ℝ] E₃ := mfderiv Ic (𝓡 3) (phi ∘ N.coordinate_map) z
    let G : E₃ →L[ℝ] E₃ →L[ℝ] ℝ := g'.inner ((phi ∘ N.coordinate_map) z)
    H • G.bilinearComp D D
  let D : RoundCylinderSpace → V →L[ℝ] V →L[ℝ] ℝ := fun z =>
    let D' : V →L[ℝ] E₃ := mfderiv Ic (𝓡 3) N.coordinate_map z
    let G : E₃ →L[ℝ] E₃ →L[ℝ] ℝ := (S.metric (s + u / H)).inner (N.coordinate_map z)
    H • G.bilinearComp D' D'
  have hB : RoundCylinderTensorSmoothOn N.epsilon (fun z v w => B z v w) :=
    (capPersistence_roundCylinderTensorSmoothOn_pullback g' hcoord).const_mul
  have hD : RoundCylinderTensorSmoothOn N.epsilon (fun z v w => D z v w) :=
    (capPersistence_roundCylinderTensorSmoothOn_pullback
      (S.metric (s + u / H)) N.coordinate_map_smooth).const_mul
  have hb := source_recent_translation_coefficient_error_bound hdom B D hB hD m (herror u hu)
  intro q0 r hr j hj a b
  simp only [sourceRecentCapTensor, dif_pos hu]
  change ‖iteratedFDeriv ℝ j (fun y => roundCylinderTensorCoefficient
      (neckAxialTensorPullback 1 c (fun z v w => B z v w)) (chartAt E₂ q0) y a b -
      roundCylinderTensorCoefficient (neckAxialTensorPullback 1 c (fun z v w => D z v w))
        (chartAt E₂ q0) y a b) (0, r)‖ ≤ K
  exact hb q0 r hr j hj a b

end PoincareConjecture.M47
