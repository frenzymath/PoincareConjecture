import PoincareConjecture.Proofs.M47.CanonicalNeckBufferedFamily










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M47

open Proofs.M47 M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "V" => RoundCylinderCoordinates



theorem source_neck_affine_weighted_jet_le
    {lambda : ℝ} (hlambda : lambda ∈ Icc (0 : ℝ) 1)
    (c w : ℝ) (hw : |w| ≤ 1) (f : V → ℝ) (x : V) (j : ℕ)
    (hf : ContDiffAt ℝ ∞ f (neckAxialCoordinate lambda c x)) :
    ‖iteratedFDeriv ℝ j (fun y => w * f (neckAxialCoordinate lambda c y)) x‖ ≤
      ‖iteratedFDeriv ℝ j f (neckAxialCoordinate lambda c x)‖ := by
  let f' : V → ℝ := fun y => f (y + (0, c))
  have hpoint : neckAxialCoordinate lambda 0 x + (0, c) =
      neckAxialCoordinate lambda c x := by
    ext <;> simp [neckAxialCoordinate]
  have hshifted : ContDiffAt ℝ ∞ f (neckAxialCoordinate lambda 0 x + (0, c)) := by
    rw [hpoint]
    exact hf
  have hsmooth : ContDiffAt ℝ ∞ f' (neckAxialCoordinate lambda 0 x) :=
    hshifted.comp (neckAxialCoordinate lambda 0 x) (contDiffAt_id.add contDiffAt_const)
  have h := norm_iteratedFDeriv_weighted_neck_compression_le hlambda w hw f' x j hsmooth
  have hfun : (fun y => w * f (neckAxialCoordinate lambda c y)) =
      (fun y => w * f' (neckAxialCoordinate lambda 0 y)) := by
    funext y
    simp [f', neckAxialCoordinate]
  rw [hfun]
  apply h.trans_eq
  dsimp only [f']
  rw [iteratedFDeriv_comp_add_right, hpoint]



theorem source_neck_affine_coefficient_error_bound
    {epsilon lambda c K : ℝ} (hepsilon : 0 < epsilon)
    (hlambda : lambda ∈ Ioo (0 : ℝ) 1)
    (hc : |c| < (1 - lambda) * epsilon⁻¹)
    (B D : RoundCylinderSpace → V →L[ℝ] V →L[ℝ] ℝ)
    (hB : RoundCylinderTensorSmoothOn epsilon (fun z v w => B z v w))
    (hD : RoundCylinderTensorSmoothOn epsilon (fun z v w => D z v w))
    (m : ℕ)
    (herror : ∀ q : UnitTwoSphere, ∀ z ∈ Ioo (-epsilon⁻¹) epsilon⁻¹,
      ∀ j ≤ m, ∀ i l : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y =>
          roundCylinderTensorCoefficient (fun z v w => B z v w) (chartAt E₂ q) y i l -
          roundCylinderTensorCoefficient (fun z v w => D z v w) (chartAt E₂ q) y i l)
            (0, z)‖ ≤ K) :
    ∀ q : UnitTwoSphere, ∀ z ∈ Icc (-epsilon⁻¹) epsilon⁻¹,
      ∀ j ≤ m, ∀ i l : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y =>
          roundCylinderTensorCoefficient
            (neckAxialTensorPullback lambda c (fun z v w => B z v w))
            (chartAt E₂ q) y i l -
          roundCylinderTensorCoefficient
            (neckAxialTensorPullback lambda c (fun z v w => D z v w))
            (chartAt E₂ q) y i l) (0, z)‖ ≤ K := by
  intro q z hz j hj i l
  have haxis := neckAxialCoordinate_mem_open_interval hepsilon hlambda hc hz
  let f : V → ℝ := fun y =>
    roundCylinderTensorCoefficient (fun z v w => B z v w) (chartAt E₂ q) y i l -
      roundCylinderTensorCoefficient (fun z v w => D z v w) (chartAt E₂ q) y i l
  have hpoint : neckAxialCoordinate lambda c (0, z) = (0, lambda * z + c) := rfl
  have hmem : (0, lambda * z + c) ∈
      (chartAt E₂ q).target ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ := by
    refine ⟨?_, haxis⟩
    rw [roundCylinder_sphereChart_target]
    trivial
  have hf : ContDiffAt ℝ ∞ f (neckAxialCoordinate lambda c (0, z)) := by
    rw [hpoint]
    exact ((hB q i l).contDiffAt (((chartAt E₂ q).open_target.prod isOpen_Ioo).mem_nhds hmem)).sub
      ((hD q i l).contDiffAt (((chartAt E₂ q).open_target.prod isOpen_Ioo).mem_nhds hmem))
  have hweight (a : Fin 3) : |neckAxialWeight lambda a| ≤ 1 := by
    unfold neckAxialWeight
    split_ifs
    · simpa only [abs_of_pos hlambda.1] using hlambda.2.le
    · norm_num
  have hw : |neckAxialWeight lambda i * neckAxialWeight lambda l| ≤ 1 := by
    rw [abs_mul]
    simpa only [one_mul] using
      mul_le_mul (hweight i) (hweight l) (abs_nonneg _) zero_le_one
  have hfun : (fun y =>
      roundCylinderTensorCoefficient
        (neckAxialTensorPullback lambda c (fun z v w => B z v w))
        (chartAt E₂ q) y i l -
      roundCylinderTensorCoefficient
        (neckAxialTensorPullback lambda c (fun z v w => D z v w))
        (chartAt E₂ q) y i l) =
      (fun y => (neckAxialWeight lambda i * neckAxialWeight lambda l) *
        f (neckAxialCoordinate lambda c y)) := by
    funext y
    rw [roundCylinderTensorCoefficient_neckAxialTensorPullback,
      roundCylinderTensorCoefficient_neckAxialTensorPullback, ← mul_sub]
  rw [hfun]
  exact (source_neck_affine_weighted_jet_le ⟨hlambda.1.le, hlambda.2.le⟩ c _ hw
    f (0, z) j hf).trans (herror q _ haxis j hj i l)



theorem exists_source_neck_family_coefficient_tolerance
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (D : ℝ → RoundCylinderTwoTensor)
    (hD : RoundCylinderFamilyClose epsilon (Icc (-1 : ℝ) 0) D) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ B : ℝ → RoundCylinderTwoTensor,
      (∀ u ∈ Icc (-1 : ℝ) 0, RoundCylinderTensorSmoothOn epsilon (B u)) →
      (∀ u ∈ Icc (-1 : ℝ) 0, ∀ q : UnitTwoSphere,
        ∀ z ∈ Ioo (-epsilon⁻¹) epsilon⁻¹,
          ∀ j ≤ Nat.floor epsilon⁻¹, ∀ i l : Fin 3,
            ‖iteratedFDeriv ℝ j (fun y =>
              roundCylinderTensorCoefficient (B u) (chartAt E₂ q) y i l -
              roundCylinderTensorCoefficient (D u) (chartAt E₂ q) y i l)
                (0, z)‖ ≤ kappa) →
      RoundCylinderFamilyClose epsilon (Icc (-1 : ℝ) 0) B := by
  obtain ⟨eta, heta, hperturb⟩ := exists_same_epsilon_neck_family_perturbation_tolerance
    hepsilon (fun _ hu => hu.2) D hD
  let K0 : Set V := ({0} : Set E₂) ×ˢ Icc (-epsilon⁻¹) epsilon⁻¹
  obtain ⟨A, hA, hbound⟩ := exists_roundCylinder_covariant_difference_component_bound
    (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 0))
    (fun _ hu => hu.2.trans_lt zero_lt_one)
    (isCompact_singleton.prod isCompact_Icc : IsCompact K0) (Nat.floor epsilon⁻¹)
  let kappa := eta / (A + 1)
  have hkappa : 0 < kappa := div_pos heta (by positivity)
  have hsmall : A * kappa ≤ eta := by
    have hmul : (A + 1) * kappa = eta := by dsimp only [kappa]; field_simp
    nlinarith only [hmul, hkappa]
  refine ⟨kappa, hkappa, ?_⟩
  intro B hs herror
  apply hperturb B hs
  intro u hu z hz k hk v
  have hcenter : (0, z.2) ∈ (chartAt E₂ z.1).target ×ˢ
      Ioo (-epsilon⁻¹) epsilon⁻¹ := by
    refine ⟨?_, hz⟩
    simpa only [sphere_chart_center_zero] using
      (chartAt E₂ z.1).map_source (mem_chart_source E₂ z.1)
  have h := hbound u hu z.1 (B u) (D u) epsilon (hs u hu) (hD.1 u hu)
    (0, z.2) ⟨mem_singleton 0, hz.1.le, hz.2.le⟩ hcenter kappa hkappa.le
    (herror u hu z.1 z.2 hz) k hk v
  simpa only [sphere_chart_center_zero] using h.trans hsmall

end PoincareConjecture.M47
