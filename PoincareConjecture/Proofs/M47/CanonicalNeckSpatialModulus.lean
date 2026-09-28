import PoincareConjecture.Proofs.M47.CanonicalNeckSpatialTranslation









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M47

open M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "V" => RoundCylinderCoordinates



theorem exists_neck_compressed_metric_translation_modulus
    {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M]
    [IsManifold (𝓡 3) ∞ M]
    {a b : ℝ} (hab : a < b) (F : RicciFlow 3 M (Icc a b))
    {g0 : RiemannianMetric 3 M} (N : EpsilonNeck g0)
    {lambda : ℝ} (hlambda : lambda ∈ Icc 0 1)
    {R : ℝ} (hleft : lambda * N.epsilon⁻¹ < R) (hR : R < N.epsilon⁻¹)
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ c : ℝ, |c| < delta →
      |c| < R - lambda * N.epsilon⁻¹ ∧
      ∀ t ∈ Icc a b, ∀ q : UnitTwoSphere,
        ∀ z ∈ Icc (-N.epsilon⁻¹) N.epsilon⁻¹, ∀ j ≤ m, ∀ i l : Fin 3,
          ‖iteratedFDeriv ℝ j (fun y =>
            roundCylinderTensorCoefficient
                (neckAxialTensorPullback lambda c
                  (roundCylinderPullback (F.metric t) N.coordinate_map)) (chartAt E₂ q) y i l -
              roundCylinderTensorCoefficient
                (neckAxialTensorPullback lambda 0
                  (roundCylinderPullback (F.metric t) N.coordinate_map)) (chartAt E₂ q) y i l)
            (0, z)‖ < rho := by
  obtain ⟨B, hB, hbound⟩ := neck_metric_axial_jet_difference_bound hab F N hR m
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hden : 0 < B + 1 := by linarith
  let delta := min (R - lambda * N.epsilon⁻¹) (rho / (B + 1))
  have hdelta : 0 < delta := lt_min (sub_pos.mpr hleft) (div_pos hrho hden)
  refine ⟨delta, hdelta, ?_⟩
  intro c hc
  have hbuffer : |c| < R - lambda * N.epsilon⁻¹ := hc.trans_le (min_le_left _ _)
  have hsmall : B * |c| < rho := by
    have h := (lt_div_iff₀ hden).mp (hc.trans_le (min_le_right _ _))
    nlinarith only [h, abs_nonneg c]
  refine ⟨hbuffer, ?_⟩
  intro t ht q z hz j hj i l
  have hzeroabs : |lambda * z| ≤ lambda * N.epsilon⁻¹ := by
    rw [abs_mul, abs_of_nonneg hlambda.1]
    exact mul_le_mul_of_nonneg_left (abs_le.mpr hz) hlambda.1
  have hzero : lambda * z ∈ Icc (-R) R := abs_le.mp (hzeroabs.trans hleft.le)
  have hcabs : |lambda * z + c| < R := by
    calc
      _ ≤ |lambda * z| + |c| := abs_add_le _ _
      _ < lambda * N.epsilon⁻¹ + (R - lambda * N.epsilon⁻¹) :=
        add_lt_add_of_le_of_lt hzeroabs hbuffer
      _ = R := by ring
  have hshift : lambda * z + c ∈ Icc (-R) R := abs_le.mp hcabs.le
  let f : V → ℝ := fun y =>
    roundCylinderTensorCoefficient (roundCylinderPullback (F.metric t) N.coordinate_map)
      (chartAt E₂ q) y i l
  have hf (s : ℝ) (hs : s ∈ Icc (-R) R) : ContDiffAt ℝ ∞ f (0, s) := by
    apply (capPersistence_roundCylinderTensorSmoothOn_pullback
      (F.metric t) N.coordinate_map_smooth q i l).contDiffAt
    apply ((chartAt E₂ q).open_target.prod isOpen_Ioo).mem_nhds
    exact ⟨by rw [roundCylinder_sphereChart_target]; trivial,
      (neg_lt_neg hR).trans_le hs.1, hs.2.trans_lt hR⟩
  have hfc : ContDiffAt ℝ ∞ f (neckAxialCoordinate lambda c (0, z)) := hf _ hshift
  have hf0 : ContDiffAt ℝ ∞ f (neckAxialCoordinate lambda 0 (0, z)) := by
    simpa only [neckAxialCoordinate, add_zero] using hf _ hzero
  have hdiff : ‖iteratedFDeriv ℝ j f (neckAxialCoordinate lambda c (0, z)) -
      iteratedFDeriv ℝ j f (neckAxialCoordinate lambda 0 (0, z))‖ ≤ B * |c| := by
    simpa only [f, neckAxialCoordinate, add_zero, add_sub_cancel_left] using
      hbound t ht q _ hshift _ hzero j hj i l
  let A : V → ℝ := fun y => f (neckAxialCoordinate lambda c y) -
    f (neckAxialCoordinate lambda 0 y)
  have hAjet : ‖iteratedFDeriv ℝ j A (0, z)‖ ≤ B * |c| := by
    apply (norm_iteratedFDeriv_neck_axial_difference_le lambda c f (0, z) j hfc hf0).trans
    calc
      _ ≤ (B * |c|) * 1 := mul_le_mul hdiff
        (pow_le_one₀ (norm_nonneg _) (norm_neckAxialLinearMap_le_one hlambda))
        (pow_nonneg (norm_nonneg _) _) (mul_nonneg hB0 (abs_nonneg c))
      _ = _ := mul_one _
  have hcoord (d : ℝ) : ContDiff ℝ ∞ (neckAxialCoordinate lambda d) :=
    contDiff_fst.prodMk ((contDiff_const.mul contDiff_snd).add contDiff_const)
  have hA : ContDiffAt ℝ ∞ A (0, z) :=
    (hfc.comp (0, z) (hcoord c).contDiffAt).sub
      (hf0.comp (0, z) (hcoord 0).contDiffAt)
  let w := neckAxialWeight lambda i * neckAxialWeight lambda l
  have hw (k : Fin 3) : |neckAxialWeight lambda k| ≤ 1 := by
    unfold neckAxialWeight
    split_ifs
    · simpa only [abs_of_nonneg hlambda.1] using hlambda.2
    · norm_num
  have hw1 : |w| ≤ 1 := by
    dsimp only [w]
    rw [abs_mul]
    exact (mul_le_mul (hw i) (hw l) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  let G : RoundCylinderSpace → V →L[ℝ] V →L[ℝ] ℝ := fun z =>
    let G0 : E₃ →L[ℝ] E₃ →L[ℝ] ℝ := (F.metric t).inner (N.coordinate_map z)
    let D : V →L[ℝ] E₃ := mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z
    G0.bilinearComp D D
  have hcoeff (d : ℝ) (y : V) : roundCylinderTensorCoefficient
      (neckAxialTensorPullback lambda d (roundCylinderPullback (F.metric t) N.coordinate_map))
      (chartAt E₂ q) y i l = w * f (neckAxialCoordinate lambda d y) :=
    roundCylinderTensorCoefficient_neckAxialTensorPullback lambda d G q y i l
  have heq : (fun y => roundCylinderTensorCoefficient
        (neckAxialTensorPullback lambda c (roundCylinderPullback (F.metric t) N.coordinate_map))
          (chartAt E₂ q) y i l -
      roundCylinderTensorCoefficient
        (neckAxialTensorPullback lambda 0 (roundCylinderPullback (F.metric t) N.coordinate_map))
          (chartAt E₂ q) y i l) = fun y => w • A y := by
    funext y
    rw [hcoeff, hcoeff]
    simp only [A, smul_eq_mul, mul_sub]
  rw [heq, iteratedFDeriv_const_smul_apply' (hA.of_le (by exact_mod_cast le_top)), norm_smul]
  calc
    _ ≤ 1 * ‖iteratedFDeriv ℝ j A (0, z)‖ := mul_le_mul_of_nonneg_right hw1 (norm_nonneg _)
    _ ≤ B * |c| := by simpa only [one_mul] using hAjet
    _ < rho := hsmall

end PoincareConjecture.Proofs.M47
