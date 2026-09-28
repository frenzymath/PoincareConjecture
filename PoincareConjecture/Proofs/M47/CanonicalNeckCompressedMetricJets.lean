import PoincareConjecture.Proofs.M47.CanonicalNeckBufferTimeModulus
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


theorem neck_metric_coefficient_axial_pullback
    {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M]
    [IsManifold (𝓡 3) ∞ M] (g : RiemannianMetric 3 M)
    (coordinate : RoundCylinderSpace → M) (lambda c : ℝ)
    (q : UnitTwoSphere) (y : V) (i l : Fin 3) :
    roundCylinderTensorCoefficient
        (neckAxialTensorPullback lambda c (roundCylinderPullback g coordinate))
        (chartAt E₂ q) y i l =
      neckAxialWeight lambda i * neckAxialWeight lambda l *
        roundCylinderTensorCoefficient (roundCylinderPullback g coordinate)
          (chartAt E₂ q) (neckAxialCoordinate lambda c y) i l := by
  let G : RoundCylinderSpace → V →L[ℝ] V →L[ℝ] ℝ := fun z =>
    let G0 : E₃ →L[ℝ] E₃ →L[ℝ] ℝ := g.inner (coordinate z)
    let D : V →L[ℝ] E₃ := mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z
    G0.bilinearComp D D
  exact roundCylinderTensorCoefficient_neckAxialTensorPullback lambda c G q y i l

private theorem axial_weight_product_abs_le_one {lambda : ℝ}
    (hlambda : lambda ∈ Icc 0 1) (i l : Fin 3) :
    |neckAxialWeight lambda i * neckAxialWeight lambda l| ≤ 1 := by
  have hw (k : Fin 3) : |neckAxialWeight lambda k| ≤ 1 := by
    unfold neckAxialWeight
    split_ifs
    · simpa only [abs_of_nonneg hlambda.1] using hlambda.2
    · norm_num
  rw [abs_mul]
  exact (mul_le_mul (hw i) (hw l) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)



theorem norm_iteratedFDeriv_weighted_neck_compression_le
    {lambda : ℝ} (hlambda : lambda ∈ Icc 0 1) (w : ℝ) (hw : |w| ≤ 1)
    (f : V → ℝ) (x : V) (j : ℕ)
    (hf : ContDiffAt ℝ ∞ f (neckAxialCoordinate lambda 0 x)) :
    ‖iteratedFDeriv ℝ j (fun y => w * f (neckAxialCoordinate lambda 0 y)) x‖ ≤
      ‖iteratedFDeriv ℝ j f (neckAxialCoordinate lambda 0 x)‖ := by
  let L := neckAxialLinearMap lambda
  have heq : neckAxialCoordinate lambda 0 = L := by
    funext y
    ext <;> simp [L, neckAxialLinearMap, neckAxialCoordinate]
  have hfL : ContDiffAt ℝ ∞ f (L x) := by rwa [heq] at hf
  have hcomp : ContDiffAt ℝ ∞ (f ∘ L) x := hfL.comp x L.contDiff.contDiffAt
  have hjet := L.norm_iteratedFDeriv_comp_right_of_contDiffAt
    (hfL.of_le (by exact_mod_cast le_top) : ContDiffAt ℝ (j : ℕ∞ω) f (L x))
  rw [heq]
  change ‖iteratedFDeriv ℝ j (fun y => w • (f ∘ L) y) x‖ ≤
    ‖iteratedFDeriv ℝ j f (L x)‖
  rw [iteratedFDeriv_const_smul_apply' (hcomp.of_le (by exact_mod_cast le_top)), norm_smul]
  calc
    _ ≤ 1 * ‖iteratedFDeriv ℝ j (f ∘ L) x‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg _)
    _ ≤ ‖iteratedFDeriv ℝ j f (L x)‖ * ‖L‖ ^ j := by simpa only [one_mul] using hjet
    _ ≤ ‖iteratedFDeriv ℝ j f (L x)‖ * 1 := mul_le_mul_of_nonneg_left
      (pow_le_one₀ (norm_nonneg _) (norm_neckAxialLinearMap_le_one hlambda)) (norm_nonneg _)
    _ = _ := mul_one _

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M]
  [IsManifold (𝓡 3) ∞ M]

private theorem compressed_axial_mem {epsilon lambda R z : ℝ}
    (hlambda : 0 ≤ lambda) (hleft : lambda * epsilon⁻¹ ≤ R)
    (hz : z ∈ Icc (-epsilon⁻¹) epsilon⁻¹) : lambda * z ∈ Icc (-R) R := by
  apply abs_le.mp
  rw [abs_mul, abs_of_nonneg hlambda]
  exact (mul_le_mul_of_nonneg_left (abs_le.mpr hz) hlambda).trans hleft

private theorem coefficient_smooth_at_axial_point
    {g0 : RiemannianMetric 3 M} (N : EpsilonNeck g0) (g : RiemannianMetric 3 M)
    (q : UnitTwoSphere) (i l : Fin 3) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ContDiffAt ℝ ∞ (fun y => roundCylinderTensorCoefficient
      (roundCylinderPullback g N.coordinate_map) (chartAt E₂ q) y i l) (0, s) := by
  apply (capPersistence_roundCylinderTensorSmoothOn_pullback
    g N.coordinate_map_smooth q i l).contDiffAt
  apply ((chartAt E₂ q).open_target.prod isOpen_Ioo).mem_nhds
  exact ⟨by rw [roundCylinder_sphereChart_target]; trivial, hs⟩



theorem compressed_neck_metric_coefficient_contDiffAt
    {g0 : RiemannianMetric 3 M} (N : EpsilonNeck g0) (g : RiemannianMetric 3 M)
    (lambda c : ℝ) (q : UnitTwoSphere) (z : ℝ) (i l : Fin 3)
    (hz : lambda * z + c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ContDiffAt ℝ ∞ (fun y => roundCylinderTensorCoefficient
      (neckAxialTensorPullback lambda c (roundCylinderPullback g N.coordinate_map))
      (chartAt E₂ q) y i l) (0, z) := by
  have hf := coefficient_smooth_at_axial_point N g q i l hz
  have hcoord : ContDiff ℝ ∞ (neckAxialCoordinate lambda c) :=
    contDiff_fst.prodMk ((contDiff_const.mul contDiff_snd).add contDiff_const)
  have hcomp := hf.comp (0, z) hcoord.contDiffAt
  have heq : (fun y => roundCylinderTensorCoefficient
      (neckAxialTensorPullback lambda c (roundCylinderPullback g N.coordinate_map))
      (chartAt E₂ q) y i l) = fun y => neckAxialWeight lambda i * neckAxialWeight lambda l *
        roundCylinderTensorCoefficient (roundCylinderPullback g N.coordinate_map)
          (chartAt E₂ q) (neckAxialCoordinate lambda c y) i l := by
    funext y
    exact neck_metric_coefficient_axial_pullback g N.coordinate_map lambda c q y i l
  rw [heq]
  exact contDiffAt_const.mul hcomp



theorem compressed_neck_metric_coefficient_jets_bounded
    {a b : ℝ} (hab : a < b) (F : RicciFlow 3 M (Icc a b))
    {g0 : RiemannianMetric 3 M} (N : EpsilonNeck g0)
    {lambda : ℝ} (hlambda : lambda ∈ Icc 0 1)
    {R : ℝ} (hleft : lambda * N.epsilon⁻¹ ≤ R) (hR : R < N.epsilon⁻¹) (m : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ t ∈ Icc a b, ∀ q : UnitTwoSphere,
      ∀ z ∈ Icc (-N.epsilon⁻¹) N.epsilon⁻¹, ∀ j ≤ m, ∀ i l : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y => roundCylinderTensorCoefficient
          (neckAxialTensorPullback lambda 0 (roundCylinderPullback (F.metric t) N.coordinate_map))
          (chartAt E₂ q) y i l) (0, z)‖ ≤ B := by
  obtain ⟨B, hB, hbound⟩ := neck_metric_jets_bounded_on_closed_cylinder hab F N hR m
  refine ⟨B, hB, ?_⟩
  intro t ht q z hz j hj i l
  have hshort := compressed_axial_mem hlambda.1 hleft hz
  have hopen : lambda * z ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨(neg_lt_neg hR).trans_le hshort.1, hshort.2.trans_lt hR⟩
  let f : V → ℝ := fun y => roundCylinderTensorCoefficient
    (roundCylinderPullback (F.metric t) N.coordinate_map) (chartAt E₂ q) y i l
  have hf : ContDiffAt ℝ ∞ f (neckAxialCoordinate lambda 0 (0, z)) := by
    simpa only [neckAxialCoordinate, add_zero] using
      coefficient_smooth_at_axial_point N (F.metric t) q i l hopen
  have h := norm_iteratedFDeriv_weighted_neck_compression_le hlambda
    (neckAxialWeight lambda i * neckAxialWeight lambda l)
    (axial_weight_product_abs_le_one hlambda i l) f (0, z) j hf
  have heq : (fun y => roundCylinderTensorCoefficient
      (neckAxialTensorPullback lambda 0 (roundCylinderPullback (F.metric t) N.coordinate_map))
      (chartAt E₂ q) y i l) = fun y => neckAxialWeight lambda i * neckAxialWeight lambda l *
        f (neckAxialCoordinate lambda 0 y) := by
    funext y
    exact neck_metric_coefficient_axial_pullback (F.metric t) N.coordinate_map lambda 0 q y i l
  rw [heq]
  exact h.trans (by
    simpa only [f, neckAxialCoordinate, add_zero] using hbound t ht q _ hshort j hj i l)



theorem compressed_neck_metric_jets_uniform_time_delta [T3Space M]
    {a b : ℝ} (hab : a < b) (F : RicciFlow 3 M (Icc a b))
    {g0 : RiemannianMetric 3 M} (N : EpsilonNeck g0)
    {lambda : ℝ} (hlambda : lambda ∈ Icc 0 1)
    {R : ℝ} (hleft : lambda * N.epsilon⁻¹ ≤ R) (hR : R < N.epsilon⁻¹)
    (m : ℕ) (hm : m ≤ Nat.floor N.epsilon⁻¹) {rho : ℝ} (hrho : 0 < rho) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      |s - t| < delta → ∀ q : UnitTwoSphere,
        ∀ z ∈ Icc (-N.epsilon⁻¹) N.epsilon⁻¹, ∀ j ≤ m, ∀ i l : Fin 3,
          ‖iteratedFDeriv ℝ j (fun y =>
            roundCylinderTensorCoefficient
                (neckAxialTensorPullback lambda 0
                  (roundCylinderPullback (F.metric s) N.coordinate_map)) (chartAt E₂ q) y i l -
              roundCylinderTensorCoefficient
                (neckAxialTensorPullback lambda 0
                  (roundCylinderPullback (F.metric t) N.coordinate_map)) (chartAt E₂ q) y i l)
            (0, z)‖ < rho := by
  obtain ⟨delta, hdelta, hmod⟩ := neck_buffer_metric_jets_uniform_time_delta hab F N hR m hm hrho
  refine ⟨delta, hdelta, ?_⟩
  intro s hs t ht hst q z hz j hj i l
  have hshort := compressed_axial_mem hlambda.1 hleft hz
  have hopen : lambda * z ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨(neg_lt_neg hR).trans_le hshort.1, hshort.2.trans_lt hR⟩
  let f : V → ℝ := fun y =>
    roundCylinderTensorCoefficient (roundCylinderPullback (F.metric s) N.coordinate_map)
        (chartAt E₂ q) y i l -
      roundCylinderTensorCoefficient (roundCylinderPullback (F.metric t) N.coordinate_map)
        (chartAt E₂ q) y i l
  have hf : ContDiffAt ℝ ∞ f (neckAxialCoordinate lambda 0 (0, z)) := by
    simpa only [neckAxialCoordinate, add_zero] using
      (coefficient_smooth_at_axial_point N (F.metric s) q i l hopen).sub
        (coefficient_smooth_at_axial_point N (F.metric t) q i l hopen)
  have h := norm_iteratedFDeriv_weighted_neck_compression_le hlambda
    (neckAxialWeight lambda i * neckAxialWeight lambda l)
    (axial_weight_product_abs_le_one hlambda i l) f (0, z) j hf
  have heq : (fun y => roundCylinderTensorCoefficient
      (neckAxialTensorPullback lambda 0 (roundCylinderPullback (F.metric s) N.coordinate_map))
        (chartAt E₂ q) y i l -
      roundCylinderTensorCoefficient
        (neckAxialTensorPullback lambda 0 (roundCylinderPullback (F.metric t) N.coordinate_map))
        (chartAt E₂ q) y i l) = fun y => neckAxialWeight lambda i * neckAxialWeight lambda l *
          f (neckAxialCoordinate lambda 0 y) := by
    funext y
    rw [neck_metric_coefficient_axial_pullback, neck_metric_coefficient_axial_pullback]
    simp only [f, mul_sub]
  rw [heq]
  exact h.trans_lt (by
    simpa only [f, neckAxialCoordinate, add_zero] using hmod s hs t ht hst q _ hshort j hj i l)

end PoincareConjecture.Proofs.M47
