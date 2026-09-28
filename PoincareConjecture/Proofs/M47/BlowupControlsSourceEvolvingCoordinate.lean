import PoincareConjecture.Proofs.M47.BlowupControlsSourceEvolvingTensor
import PoincareConjecture.Proofs.M47.BlowupControlsCapAffineFields

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M47

local notation "E" => StandardCapSpace
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "Ic" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

private theorem source_affine_metric_pullback
    {X : Type u} [TopologicalSpace X] [ChartedSpace E₃ X] [IsManifold (𝓡 3) ∞ X]
    (g : RiemannianMetric 3 X) (f : RoundCylinderSpace → X)
    (lambda c : ℝ) (z : RoundCylinderSpace)
    (hf : MDifferentiableAt Ic (𝓡 3) f (neckAxialSpaceMap lambda c z))
    (v w : RoundCylinderTangent z) :
    roundCylinderPullback g (f ∘ neckAxialSpaceMap lambda c) z v w =
      neckAxialTensorPullback lambda c (roundCylinderPullback g f) z v w := by
  have hA : MDifferentiableAt Ic Ic (neckAxialSpaceMap lambda c) z :=
    (neckAxialSpaceMap_contMDiff lambda c).contMDiffAt.mdifferentiableAt (by simp)
  have hchain := mfderiv_comp z hf hA
  simp only [roundCylinderPullback, neckAxialTensorPullback, Function.comp_apply,
    hchain, ContinuousLinearMap.comp_apply, neckAxialSpaceMap_mfderiv]

theorem sourceCapNeckTensor_affine_coordinate
    {F : SurgeryFlowData.{u}} {t : ℝ} {hT : t ∈ F.surgery_times}
    [Nonempty (F.slice t).carrier] {i : Fin (F.event t hT).cap_count} {A : ℝ}
    {S : MaximalStandardCapFlow F.standard_initial} {eta : ℝ}
    {J : Set ℝ} {U : Set (F.slice t).carrier}
    (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
    (initial : SurgeryCapInitialComparison F t hT i A)
    (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
    (hh : 0 < F.parameters.h t) {g g' : RiemannianMetric 3 E}
    (N : EpsilonNeck g) (N' : EpsilonNeck g')
    (hsource : N.carrier ⊆ F.standard_initial.metric.ball 0 A)
    (sigma : ℝ → ℝ) (hclock : MapsTo sigma (Icc (-1 : ℝ) 0) J)
    (rho lambda c : ℝ) (hlambda : lambda ∈ Ioo (0 : ℝ) 1)
    (hc : |c| < (1 - lambda) * N.epsilon⁻¹)
    (hcoordinate : N'.coordinate_map = N.coordinate_map ∘ neckAxialSpaceMap lambda c)
    (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 0) {z : RoundCylinderSpace}
    (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (v w : RoundCylinderTangent z) :
    sourceCapNeckTensor e initial comparison hh N' sigma hclock rho 1 0 u z v w =
      sourceCapNeckTensor e initial comparison hh N sigma hclock rho lambda c u z v w := by
  let phi := actualCapSliceChart e initial comparison (sigma u) (hclock hu)
  let q := (F.parameters.h t)⁻¹ ^ 2
  let metric := m01RescaledMetric (F.metric (t + sigma u / q)) q
    (sq_pos_of_pos (inv_pos.mpr hh))
  have haxis := neckAxialCoordinate_mem_open_interval N.epsilon_pos hlambda hc
    ⟨hz.1.le, hz.2.le⟩
  have hzN : N.coordinate_map (neckAxialSpaceMap lambda c z) ∈ N.carrier :=
    N.coordinate_map_mem_of_axial_mem haxis
  have hphi : N.coordinate_map (neckAxialSpaceMap lambda c z) ∈ phi.source := by
    rw [actualCapSliceChart_source]
    exact hsource hzN
  have hNd := (N.coordinate_map_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds
      (show neckAxialSpaceMap lambda c z ∈ univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ from
        ⟨mem_univ _, haxis⟩))).mdifferentiableAt (by simp)
  have hphid := (phi.contMDiffOn_toFun.contMDiffAt
    (phi.open_source.mem_nhds hphi)).mdifferentiableAt (by simp)
  have hcomposed : MDifferentiableAt Ic (𝓡 3) (phi ∘ N.coordinate_map)
      (neckAxialSpaceMap lambda c z) := hphid.comp _ hNd
  have hunit (T : RoundCylinderTwoTensor) : neckAxialTensorPullback 1 0 T = T := by
    have hA (p : RoundCylinderSpace) : neckAxialSpaceMap 1 0 p = p := by
      ext <;> simp [neckAxialSpaceMap]
    have hL (a : RoundCylinderCoordinates) : neckAxialLinearMap 1 a = a := by
      ext <;> simp [neckAxialLinearMap]
    funext p a b
    simp only [neckAxialTensorPullback, hL]
    exact congrArg (fun y : RoundCylinderSpace => T y a b) (hA p)
  simp only [sourceCapNeckTensor, dif_pos hu, hunit, hcoordinate]
  change rho * roundCylinderPullback metric
      ((phi ∘ N.coordinate_map) ∘ neckAxialSpaceMap lambda c) z v w =
    rho * neckAxialTensorPullback lambda c
      (roundCylinderPullback metric (phi ∘ N.coordinate_map)) z v w
  exact congrArg (rho * ·)
    (source_affine_metric_pullback metric (phi ∘ N.coordinate_map) lambda c z hcomposed v w)

end PoincareConjecture.M47
