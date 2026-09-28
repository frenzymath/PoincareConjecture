import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckUniformMetricJets
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckPullbackSmooth
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckCovariantDifference
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckPerturbation











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology
open Poincare.Geometry.Riemannian.SpaceForm

universe u

namespace PoincareConjecture.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E₃ M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}
  (R : OrdinaryProductRicciGeometry F.metric I)

local notation "G" => ordinaryChapter11Flow (I := I) (F := F) R

private local instance {K : Set ℝ} {L : BlowupLimitFlow.{u} K} :
    TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
private local instance {K : Set ℝ} {L : BlowupLimitFlow.{u} K} :
    ChartedSpace E₃ L.carrier.carrier := L.carrier.chartedSpace
private local instance {K : Set ℝ} {L : BlowupLimitFlow.{u} K} :
    IsManifold (𝓡 3) ∞ L.carrier.carrier := L.carrier.isManifold




theorem ordinaryChapter11_eventually_neck_familyClose
    (p : ℕ → (G).point) (hpositive : ∀ k, 0 < (G).scalar (p k))
    (hdiverges : Tendsto (fun k => (G).scalar (p k)) atTop atTop) {J : Set ℝ}
    (C : GeneralizedBlowupConvergence
      (fixedFlowBlowupSequence (G) p hpositive hdiverges) J)
    (hJ : UniqueDiffOn ℝ J) (hJI : Icc (-1 : ℝ) 0 ⊆ J)
    (N : EpsilonNeck (C.limit.flow.metric 0))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hdelta : N.epsilon ≤ epsilon / 4)
    (hlimit : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (fun s => roundCylinderPullback (C.limit.flow.metric s) N.coordinate_map)) :
    ∀ᶠ k : ℕ in atTop, RoundCylinderFamilyClose epsilon (Ioc (-1 : ℝ) 0)
      (generalizedCylinderPullback (C.embedding k) N.coordinate_map) := by
  have hstrict : N.epsilon < epsilon := by linarith
  have hinv : epsilon⁻¹ < N.epsilon⁻¹ := inv_strictAnti₀ N.epsilon_pos hstrict
  let m : ℕ := ⌊epsilon⁻¹⌋₊
  let K : Set RoundCylinderCoordinates := ({0} : Set E₂) ×ˢ Icc (-epsilon⁻¹) epsilon⁻¹
  have hK : IsCompact K := isCompact_singleton.prod isCompact_Icc
  obtain ⟨A, hA, hcov⟩ := exists_roundCylinder_covariant_difference_component_bound
    (I := Icc (-1 : ℝ) 0) isCompact_Icc (fun _ hu => hu.2.trans_lt zero_lt_one) hK m
  obtain ⟨eta, heta, hperturb⟩ := exists_roundCylinderFamilyClose_perturbation_tolerance hepsilon
  let rho := eta / (A + 1)
  have hrho : 0 < rho := div_pos heta (by linarith)
  have hsmall : A * rho ≤ eta := by
    have hscale : (A + 1) * rho = eta := by
      dsimp [rho]
      field_simp
    nlinarith
  have hcoordinate : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ N.coordinate_map
      (univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹) :=
    N.coordinate_map_smooth.mono (fun z hz =>
      ⟨hz.1, lt_of_le_of_lt (neg_le_neg hinv.le) hz.2.1, hz.2.2.trans_le hinv.le⟩)
  filter_upwards [ordinaryChapter11_uniform_neck_coefficientJets R p hpositive hdiverges C
    hJ hJI N hinv m rho hrho,
    C.eventually_captures_closed_neck (C.limit.flow.metric 0) N hinv hJI]
    with k hjets hcapture
  let B := generalizedCylinderPullback (C.embedding k) N.coordinate_map
  let D := fun s => roundCylinderPullback (C.limit.flow.metric s) N.coordinate_map
  have hBs (s : ℝ) (hs : s ∈ Ioc (-1 : ℝ) 0) : RoundCylinderTensorSmoothOn epsilon (B s) :=
    generalizedCylinderPullback_roundCylinderTensorSmoothOn (C.embedding k)
      (C.exhaustion.space_open k) hcoordinate
      (fun z hz => hcapture.1 ⟨z, ⟨mem_univ _, hz.2.1.le, hz.2.2.le⟩, rfl⟩)
      (hcapture.2 ⟨hs.1.le, hs.2⟩)
  apply hperturb N.epsilon_pos hdelta (fun _ hu => hu.2) B D hlimit hBs
  intro s hs z hz j hj a
  have hDs : RoundCylinderTensorSmoothOn epsilon (D s) :=
    (hlimit.1 s hs).mono_epsilon N.epsilon_pos hstrict.le
  have hzero : chartAt E₂ z.1 z.1 = 0 := by
    have h := (chartAt E₂ z.1).right_inv
      (show (0 : E₂) ∈ (chartAt E₂ z.1).target from by
        rw [roundCylinder_sphereChart_target]
        trivial)
    rwa [sphere_chart_symm_zero] at h
  have h := hcov s ⟨hs.1.le, hs.2⟩ z.1 (B s) (D s) epsilon (hBs s hs) hDs
    (0, z.2) ⟨rfl, hz.1.le, hz.2.le⟩
    ⟨by rw [roundCylinder_sphereChart_target]; trivial, hz⟩ rho hrho.le
    (fun l hl i b => (hjets z ⟨hz.1.le, hz.2.le⟩ s ⟨hs.1.le, hs.2⟩ l hl i b).le)
    j hj a
  simpa only [hzero] using h.trans hsmall

end PoincareConjecture.M34
