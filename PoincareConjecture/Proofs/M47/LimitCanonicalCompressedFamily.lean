import PoincareConjecture.Proofs.M47.CanonicalNeckOrdinaryFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M47

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "V₃" => RoundCylinderCoordinates

variable {J : Set ℝ} (L : BlowupLimitFlow.{u} J)

private local instance : TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
private local instance : ChartedSpace E₃ L.carrier.carrier := L.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ L.carrier.carrier := L.carrier.isManifold

theorem limitCanonical_exists_compressed_limit_family
    (N : EpsilonNeck (L.flow.metric 0)) (hcenter : N.center = L.base)
    (hfamily : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (fun s => roundCylinderPullback (L.flow.metric s) N.coordinate_map)) :
    ∃ N' : EpsilonNeck (L.flow.metric 0),
      N'.epsilon = N.epsilon ∧ N'.center = L.base ∧
      N'.connection = L.flow.connection 0 ∧ N'.scale = 1 ∧
      ∃ K : Set L.sliceCarrier.carrier, IsCompact K ∧ N'.carrier ⊆ K ∧
        RoundCylinderFamilyClose N'.epsilon (Ioc (-1 : ℝ) 0)
          (fun s => roundCylinderPullback (L.flow.metric s) N'.coordinate_map) := by
  let B : ℝ → RoundCylinderSpace → V₃ →L[ℝ] V₃ →L[ℝ] ℝ := fun s z =>
    let g : E₃ →L[ℝ] E₃ →L[ℝ] ℝ := (L.flow.metric s).inner (N.coordinate_map z)
    let d : V₃ →L[ℝ] E₃ :=
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z
    g.bilinearComp d d
  have hB : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (fun s z v w => B s z v w) := hfamily
  obtain ⟨lambda, hlambda, hcompress⟩ := exists_same_epsilon_neck_axial_compression
    N.epsilon_pos (fun _ hs => hs.2) B hB
  have hzero : |(0 : ℝ)| < (1 - lambda) * N.epsilon⁻¹ := by
    rw [abs_zero]
    exact mul_pos (sub_pos.mpr hlambda.2) (inv_pos.mpr N.epsilon_pos)
  have hnormalized : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (fun s => roundCylinderPullback (L.flow.metric s)
        (N.coordinate_map ∘ neckAxialSpaceMap lambda 0)) := by
    apply (hcompress 0 hzero).congr_cylinder
    intro s _hs z hz v w
    exact compressed_neck_metric_pullback N _ hlambda hzero hz v w
  have hc : N.center ∈ N.carrier :=
    N.central_sphere_subset N.center_on_central_sphere
  have hheight : (N.coordinate_inverse N.center).2 = 0 := by
    have hmem := N.center_on_central_sphere
    rw [N.central_sphere_eq] at hmem
    obtain ⟨⟨q, z⟩, ⟨_hq, hz⟩, hpoint⟩ := hmem
    have hz0 : z = 0 := hz
    subst z
    have haxis : (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
      ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
    rw [← hpoint]
    exact congrArg Prod.snd (N.coordinate_inverse_coordinate_map_of_axial_mem (z := (q, 0)) haxis)
  have hscalar : (L.flow.connection 0).scalarCurvature N.center = 1 := by
    rw [hcenter]
    exact L.scalar_normalized
  have h0 : (0 : ℝ) ∈ Ioc (-1 : ℝ) 0 := by constructor <;> norm_num
  have hclose : RoundCylinderClose N.epsilon 0 (fun z v w =>
      (L.flow.connection 0).scalarCurvature N.center *
        roundCylinderPullback (L.flow.metric 0)
          (N.coordinate_map ∘ neckAxialSpaceMap lambda 0) z v w) := by
    rw [hscalar]
    simpa only [one_mul] using
      (show RoundCylinderClose N.epsilon 0
        (roundCylinderPullback (L.flow.metric 0)
          (N.coordinate_map ∘ neckAxialSpaceMap lambda 0)) from
        ⟨hnormalized.1 0 h0, hnormalized.2.choose, hnormalized.2.choose_spec.1,
          hnormalized.2.choose_spec.2 0 h0⟩)
  obtain ⟨N', hepsilon, hcenter', _hcarrier, hcoordinate, _hinverse,
    _hsphere, hconnection, _hcoord⟩ :=
    exists_compressed_neck_of_normalized_comparison N hlambda hzero N.center hc hheight
      (L.flow.connection 0) (by rw [hscalar]; norm_num) hclose
  have hscale : N'.scale = 1 := by
    rw [N'.scale_eq_scalar, hconnection, hcenter', hscalar]
    norm_num
  let S := neckAxialSpaceMap lambda 0 '' (univ ×ˢ Icc (-N.epsilon⁻¹) N.epsilon⁻¹)
  let K := N.coordinate_map '' S
  have hS := isCompact_neckAxialSpaceMap_closed_cylinder N.epsilon_pos hlambda hzero
  have hK : IsCompact K := hS.1.image_of_continuousOn
    (N.coordinate_map_smooth.continuousOn.mono hS.2)
  refine ⟨N', hepsilon, hcenter'.trans hcenter, hconnection, hscale, K, hK, ?_, ?_⟩
  · intro y hy
    let z := N'.coordinate_inverse y
    have hz := (N'.coordinate_inverse_mem y hy).2
    rw [hepsilon] at hz
    have hpoint : N'.coordinate_map z = y := by
      have h := congrArg (fun p : N'.carrier => (p : L.carrier.carrier))
        (N'.coordinate_inverse_right y hy)
      rw [N'.coordinate_map_eq] at h
      exact h
    refine ⟨neckAxialSpaceMap lambda 0 z,
      ⟨z, ⟨mem_univ _, hz.1.le, hz.2.le⟩, rfl⟩, ?_⟩
    exact (congrFun hcoordinate z).symm.trans hpoint
  · rw [hepsilon, hcoordinate]
    exact hnormalized

end PoincareConjecture.M47
