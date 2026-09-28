import PoincareConjecture.Proofs.M47.BlowupControlsSourceEvolvingError
import PoincareConjecture.Proofs.M47.BlowupControlsSourceEvolvingAffine









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M47

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
  (sigma : ℝ → ℝ) (hclock : MapsTo sigma (Icc (-1 : ℝ) 0) J)
  (rho lambda c : ℝ)



noncomputable def sourceCapNeckTensor : ℝ → RoundCylinderTwoTensor :=
  fun u => if hu : u ∈ Icc (-1 : ℝ) 0 then
    let hs := hclock hu
    let phi := actualCapSliceChart e initial comparison (sigma u) hs
    let Q := (F.parameters.h t)⁻¹ ^ 2
    let g' := m01RescaledMetric (F.metric (t + sigma u / Q)) Q
      (sq_pos_of_pos (inv_pos.mpr hh))
    fun z v w => rho * neckAxialTensorPullback lambda c
      (roundCylinderPullback g' (phi ∘ N.coordinate_map)) z v w
  else fun _ _ _ => 0



theorem sourceCapNeckTensor_smooth
    (hsource : N.carrier ⊆ F.standard_initial.metric.ball 0 A)
    (hlambda : lambda ∈ Ioo (0 : ℝ) 1)
    (hc : |c| < (1 - lambda) * N.epsilon⁻¹) :
    ∀ u ∈ Icc (-1 : ℝ) 0, RoundCylinderTensorSmoothOn N.epsilon
      (sourceCapNeckTensor e initial comparison hh N sigma hclock rho lambda c u) := by
  intro u hu
  let phi := actualCapSliceChart e initial comparison (sigma u) (hclock hu)
  let Q := (F.parameters.h t)⁻¹ ^ 2
  let g' := m01RescaledMetric (F.metric (t + sigma u / Q)) Q
    (sq_pos_of_pos (inv_pos.mpr hh))
  have hsource' : N.carrier ⊆ phi.source := by
    rw [actualCapSliceChart_source]
    exact hsource
  have hcoord : ContMDiffOn Ic (𝓡 3) ∞ (phi ∘ N.coordinate_map)
      (univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :=
    phi.contMDiffOn_toFun.comp N.coordinate_map_smooth
      (fun _ hz => hsource' (N.coordinate_map_mem_of_axial_mem hz.2))
  let B : RoundCylinderSpace → V →L[ℝ] V →L[ℝ] ℝ := fun z =>
    let T : E₃ →L[ℝ] E₃ →L[ℝ] ℝ := g'.inner ((phi ∘ N.coordinate_map) z)
    let D : V →L[ℝ] E₃ := mfderiv Ic (𝓡 3) (phi ∘ N.coordinate_map) z
    T.bilinearComp D D
  have hB : RoundCylinderTensorSmoothOn N.epsilon (fun z v w => B z v w) :=
    M34.capPersistence_roundCylinderTensorSmoothOn_pullback g' hcoord
  simp only [sourceCapNeckTensor, dif_pos hu]
  change RoundCylinderTensorSmoothOn N.epsilon
    (fun z v w => rho * neckAxialTensorPullback lambda c (fun z v w => B z v w) z v w)
  exact (roundCylinderTensorSmoothOn_neckAxialTensorPullback
    N.epsilon_pos hlambda hc B hB).const_mul



theorem sourceCapNeckTensor_coefficient_error_le
    (hsource : N.carrier ⊆ F.standard_initial.metric.ball 0 A)
    (hlambda : lambda ∈ Ioo (0 : ℝ) 1)
    (hc : |c| < (1 - lambda) * N.epsilon⁻¹)
    (m : ℕ) (K : ℝ)
    (herror : ∀ (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 0),
      let phi := actualCapSliceChart e initial comparison (sigma u) (hclock hu)
      let Q := (F.parameters.h t)⁻¹ ^ 2
      let g' := m01RescaledMetric (F.metric (t + sigma u / Q)) Q
        (sq_pos_of_pos (inv_pos.mpr hh))
      ∀ q : UnitTwoSphere, ∀ z ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹,
        ∀ j ≤ m, ∀ a b : Fin 3,
          ‖iteratedFDeriv ℝ j (fun y =>
            rho * roundCylinderTensorCoefficient
              (roundCylinderPullback g' (phi ∘ N.coordinate_map)) (chartAt E₂ q) y a b -
            rho * roundCylinderTensorCoefficient
              (roundCylinderPullback (S.metric (sigma u)) N.coordinate_map)
              (chartAt E₂ q) y a b) (0, z)‖ ≤ K) :
    ∀ u ∈ Icc (-1 : ℝ) 0, ∀ q : UnitTwoSphere,
      ∀ z ∈ Icc (-N.epsilon⁻¹) N.epsilon⁻¹,
        ∀ j ≤ m, ∀ a b : Fin 3,
          ‖iteratedFDeriv ℝ j (fun y =>
            roundCylinderTensorCoefficient
              (sourceCapNeckTensor e initial comparison hh N sigma hclock rho lambda c u)
              (chartAt E₂ q) y a b -
            rho * roundCylinderTensorCoefficient
              (neckAxialTensorPullback lambda c
                (roundCylinderPullback (S.metric (sigma u)) N.coordinate_map))
              (chartAt E₂ q) y a b) (0, z)‖ ≤ K := by
  intro u hu
  let phi := actualCapSliceChart e initial comparison (sigma u) (hclock hu)
  let Q := (F.parameters.h t)⁻¹ ^ 2
  let g' := m01RescaledMetric (F.metric (t + sigma u / Q)) Q
    (sq_pos_of_pos (inv_pos.mpr hh))
  have hsource' : N.carrier ⊆ phi.source := by
    rw [actualCapSliceChart_source]
    exact hsource
  have hcoord : ContMDiffOn Ic (𝓡 3) ∞ (phi ∘ N.coordinate_map)
      (univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :=
    phi.contMDiffOn_toFun.comp N.coordinate_map_smooth
      (fun _ hz => hsource' (N.coordinate_map_mem_of_axial_mem hz.2))
  let B : RoundCylinderSpace → V →L[ℝ] V →L[ℝ] ℝ := fun z =>
    let T : E₃ →L[ℝ] E₃ →L[ℝ] ℝ := g'.inner ((phi ∘ N.coordinate_map) z)
    let D : V →L[ℝ] E₃ := mfderiv Ic (𝓡 3) (phi ∘ N.coordinate_map) z
    rho • T.bilinearComp D D
  let D : RoundCylinderSpace → V →L[ℝ] V →L[ℝ] ℝ := fun z =>
    let T : E₃ →L[ℝ] E₃ →L[ℝ] ℝ := (S.metric (sigma u)).inner (N.coordinate_map z)
    let A : V →L[ℝ] E₃ := mfderiv Ic (𝓡 3) N.coordinate_map z
    rho • T.bilinearComp A A
  have hB : RoundCylinderTensorSmoothOn N.epsilon (fun z v w => B z v w) :=
    (M34.capPersistence_roundCylinderTensorSmoothOn_pullback g' hcoord).const_mul
  have hD : RoundCylinderTensorSmoothOn N.epsilon (fun z v w => D z v w) :=
    (M34.capPersistence_roundCylinderTensorSmoothOn_pullback
      (S.metric (sigma u)) N.coordinate_map_smooth).const_mul
  have hbound := source_neck_affine_coefficient_error_bound
    N.epsilon_pos hlambda hc B D hB hD m (herror u hu)
  intro q z hz j hj a b
  simp only [sourceCapNeckTensor, dif_pos hu]
  change ‖iteratedFDeriv ℝ j (fun y =>
      roundCylinderTensorCoefficient
        (neckAxialTensorPullback lambda c (fun z v w => B z v w)) (chartAt E₂ q) y a b -
      roundCylinderTensorCoefficient
        (neckAxialTensorPullback lambda c (fun z v w => D z v w)) (chartAt E₂ q) y a b)
      (0, z)‖ ≤ K
  exact hbound q z hz j hj a b

end PoincareConjecture.M47
