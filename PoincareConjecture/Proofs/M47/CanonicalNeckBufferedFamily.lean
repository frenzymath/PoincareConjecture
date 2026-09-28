import PoincareConjecture.Proofs.M47.CanonicalNeckBufferedJets
import PoincareConjecture.Proofs.M47.CanonicalNeckFamilyMargin
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckCovariantDifference

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M47

open M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "V" => RoundCylinderCoordinates

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M]
  [IsManifold (𝓡 3) ∞ M] [T3Space M]

theorem eventually_buffered_neck_family_of_compressed_comparison
    {a b : ℝ} (hab : a < b) (F : RicciFlow 3 M (Icc a b))
    {g0 : RiemannianMetric 3 M} (N : EpsilonNeck g0)
    {lambda : ℝ} (hlambda : lambda ∈ Ioo (0 : ℝ) 1)
    {X : Type*} [TopologicalSpace X] {T Q c : X → ℝ} {p0 : X}
    (hT : ContinuousAt T p0) (hQ : ContinuousAt Q p0) (hc : ContinuousAt c p0)
    (hc0 : c p0 = 0) (hQ0 : 0 < Q p0)
    (hbottom : a < T p0 - (Q p0)⁻¹) (htop : T p0 < b)
    (hbaseline : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (fun u z v w => Q p0 * neckAxialTensorPullback lambda 0
        (roundCylinderPullback (F.metric (T p0 + u / Q p0)) N.coordinate_map) z v w)) :
    ∀ᶠ p in 𝓝 p0, 0 < Q p ∧ |c p| < (1 - lambda) * N.epsilon⁻¹ ∧
      (∀ u ∈ Icc (-1 : ℝ) 0, T p + u / Q p ∈ Icc a b) ∧
      RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
        (fun u z v w => Q p * neckAxialTensorPullback lambda (c p)
          (roundCylinderPullback (F.metric (T p + u / Q p)) N.coordinate_map) z v w) := by
  let D : ℝ → RoundCylinderTwoTensor := fun u z v w => Q p0 *
    neckAxialTensorPullback lambda 0
      (roundCylinderPullback (F.metric (T p0 + u / Q p0)) N.coordinate_map) z v w
  obtain ⟨eta, heta, hperturb⟩ := exists_same_epsilon_neck_family_perturbation_tolerance
    N.epsilon_pos (fun _ hu => hu.2) D hbaseline
  let K0 : Set V := ({0} : Set E₂) ×ˢ Icc (-N.epsilon⁻¹) N.epsilon⁻¹
  obtain ⟨A, hA, hAbound⟩ := exists_roundCylinder_covariant_difference_component_bound
    (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 0))
    (fun _ hu => hu.2.trans_lt zero_lt_one)
    (isCompact_singleton.prod isCompact_Icc : IsCompact K0) (Nat.floor N.epsilon⁻¹)
  let rho := eta / (A + 1)
  have hrho : 0 < rho := div_pos heta (by positivity)
  have hsmall : A * rho ≤ eta := by
    have heq : (A + 1) * rho = eta := by dsimp only [rho]; field_simp
    nlinarith only [heq, hrho]
  filter_upwards [eventually_buffered_normalized_neck_jets hab F N hlambda
    hT hQ hc hc0 hQ0 hbottom htop (Nat.floor N.epsilon⁻¹) le_rfl hrho] with p hp
  let B : ℝ → RoundCylinderTwoTensor := fun u z v w => Q p *
    neckAxialTensorPullback lambda (c p)
      (roundCylinderPullback (F.metric (T p + u / Q p)) N.coordinate_map) z v w
  have hB (u : ℝ) : RoundCylinderTensorSmoothOn N.epsilon (B u) := by
    let G : RoundCylinderSpace → V →L[ℝ] V →L[ℝ] ℝ := fun z =>
      let G0 : E₃ →L[ℝ] E₃ →L[ℝ] ℝ :=
        (F.metric (T p + u / Q p)).inner (N.coordinate_map z)
      let J : V →L[ℝ] E₃ := mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z
      G0.bilinearComp J J
    have hG : RoundCylinderTensorSmoothOn N.epsilon (fun z v w => G z v w) :=
      capPersistence_roundCylinderTensorSmoothOn_pullback
        (F.metric (T p + u / Q p)) N.coordinate_map_smooth
    exact (roundCylinderTensorSmoothOn_neckAxialTensorPullback
      N.epsilon_pos hlambda hp.2.1 G hG).const_mul
  refine ⟨hp.1, hp.2.1, fun u hu => (hp.2.2 u hu).1, hperturb B (fun u _ => hB u) ?_⟩
  intro u hu z hz k hk v
  have hcenter : (0, z.2) ∈ (chartAt E₂ z.1).target ×ˢ
      Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    refine ⟨?_, hz⟩
    simpa only [sphere_chart_center_zero] using
      (chartAt E₂ z.1).map_source (mem_chart_source E₂ z.1)
  have h := hAbound u (Ioc_subset_Icc_self hu) z.1 (B u) (D u) N.epsilon (hB u)
    (hbaseline.1 u hu) (0, z.2) ⟨mem_singleton 0, hz.1.le, hz.2.le⟩ hcenter rho hrho.le
    (fun j hj i l => (hp.2.2 u (Ioc_subset_Icc_self hu)).2 z.1 z.2
      ⟨hz.1.le, hz.2.le⟩ j hj i l |>.le) k hk v
  simpa only [sphere_chart_center_zero] using h.trans hsmall

theorem exists_eventually_buffered_normalized_neck_family
    {a b : ℝ} (hab : a < b) (F : RicciFlow 3 M (Icc a b))
    {g0 : RiemannianMetric 3 M} (N : EpsilonNeck g0)
    {X : Type*} [TopologicalSpace X] {T Q c : X → ℝ} {p0 : X}
    (hT : ContinuousAt T p0) (hQ : ContinuousAt Q p0) (hc : ContinuousAt c p0)
    (hc0 : c p0 = 0) (hQ0 : 0 < Q p0)
    (hbottom : a < T p0 - (Q p0)⁻¹) (htop : T p0 < b)
    (hclose : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (fun u z v w => Q p0 *
        roundCylinderPullback (F.metric (T p0 + u / Q p0)) N.coordinate_map z v w)) :
    ∃ lambda : ℝ, lambda ∈ Ioo (0 : ℝ) 1 ∧
      ∀ᶠ p in 𝓝 p0, 0 < Q p ∧ |c p| < (1 - lambda) * N.epsilon⁻¹ ∧
        (∀ u ∈ Icc (-1 : ℝ) 0, T p + u / Q p ∈ Icc a b) ∧
        RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
          (fun u z v w => Q p * neckAxialTensorPullback lambda (c p)
            (roundCylinderPullback (F.metric (T p + u / Q p)) N.coordinate_map) z v w) := by
  let B0 : ℝ → RoundCylinderSpace → V →L[ℝ] V →L[ℝ] ℝ := fun u z =>
    let G0 : E₃ →L[ℝ] E₃ →L[ℝ] ℝ :=
      (F.metric (T p0 + u / Q p0)).inner (N.coordinate_map z)
    let J : V →L[ℝ] E₃ := mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z
    Q p0 • G0.bilinearComp J J
  have hB0 : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (fun u z v w => B0 u z v w) := hclose
  obtain ⟨lambda, hlambda, hcompression⟩ := exists_same_epsilon_neck_axial_compression
    N.epsilon_pos (fun _ hu => hu.2) B0 hB0
  have hzero : |(0 : ℝ)| < (1 - lambda) * N.epsilon⁻¹ := by
    rw [abs_zero]
    exact mul_pos (sub_pos.mpr hlambda.2) (inv_pos.mpr N.epsilon_pos)
  exact ⟨lambda, hlambda, eventually_buffered_neck_family_of_compressed_comparison
    hab F N hlambda hT hQ hc hc0 hQ0 hbottom htop (hcompression 0 hzero)⟩

end PoincareConjecture.Proofs.M47
