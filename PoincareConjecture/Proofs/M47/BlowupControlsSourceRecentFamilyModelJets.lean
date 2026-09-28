import PoincareConjecture.Proofs.M47.CanonicalNeckBufferTimeModulus
import PoincareConjecture.Proofs.M47.CanonicalNeckSpatialBounds
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_CylinderTimeComparison
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistencePullbackSmooth










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff BigOperators Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M47 M34 M36 M44

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "V" => RoundCylinderCoordinates


theorem exists_source_recent_model_coefficient_time_bound (m : ℕ) :
    ∃ Z : ℝ, 0 ≤ Z ∧ ∀ (u v : ℝ) (q : UnitTwoSphere) (r : ℝ),
      ∀ j ≤ m, ∀ a b : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y => roundCylinderGram u (chartAt E₂ q) y a b -
          roundCylinderGram v (chartAt E₂ q) y a b) (0, r)‖ ≤ Z * |u - v| := by
  let f (a b : Fin 3) : V → ℝ := fun p => cylinderSphereFactor p * cylinderHorizontalGram a b
  have hf (a b : Fin 3) : ContDiff ℝ ∞ (f a b) := cylinderSphereFactor_contDiff.mul contDiff_const
  let Z : ℝ := ∑ j : Fin (m + 1), ∑ a : Fin 3, ∑ b : Fin 3,
    ‖iteratedFDeriv ℝ j (f a b) (0 : V)‖
  have hZ : 0 ≤ Z := Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨Z, hZ, ?_⟩
  intro u v q r j hj a b
  have heq : (fun y => roundCylinderGram u (chartAt E₂ q) y a b -
      roundCylinderGram v (chartAt E₂ q) y a b) = fun y => (v - u) • f a b y := by
    funext y
    simp only [evolving_roundCylinderGram_entry, f, smul_eq_mul]
    ring
  have hshift : iteratedFDeriv ℝ j (f a b) (0, r) =
      iteratedFDeriv ℝ j (f a b) (0 : V) := by
    have hfun : (fun p : V => f a b (p + (0, r))) = f a b := by
      funext p
      simp only [f, cylinderSphereFactor, Prod.fst_add, add_zero]
    have h := congrArg (fun g : V → ℝ => iteratedFDeriv ℝ j g (0 : V)) hfun
    simpa only [iteratedFDeriv_comp_add_right, zero_add] using h
  have hbound : ‖iteratedFDeriv ℝ j (f a b) (0 : V)‖ ≤ Z := by
    let j' : Fin (m + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
    have hb := Finset.single_le_sum (s := (Finset.univ : Finset (Fin 3)))
      (fun b _ => norm_nonneg (iteratedFDeriv ℝ j (f a b) (0 : V))) (Finset.mem_univ b)
    have ha : (∑ b : Fin 3, ‖iteratedFDeriv ℝ j (f a b) (0 : V)‖) ≤
        ∑ a : Fin 3, ∑ b : Fin 3, ‖iteratedFDeriv ℝ j (f a b) (0 : V)‖ :=
      Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun b _ =>
        norm_nonneg (iteratedFDeriv ℝ j (f a b) (0 : V))) (Finset.mem_univ a)
    have hsum : (∑ a : Fin 3, ∑ b : Fin 3, ‖iteratedFDeriv ℝ j (f a b) (0 : V)‖) ≤ Z :=
      Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin (m + 1)))) (a := j')
        (f := fun k : Fin (m + 1) => ∑ a : Fin 3, ∑ b : Fin 3,
          ‖iteratedFDeriv ℝ k (f a b) (0 : V)‖)
        (fun k _ => Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
          norm_nonneg (iteratedFDeriv ℝ k (f a b) (0 : V))) (Finset.mem_univ j')
    exact (hb.trans ha).trans hsum
  rw [heq, iteratedFDeriv_const_smul_apply'
    ((hf a b).contDiffAt.of_le (by exact_mod_cast le_top)), norm_smul,
    Real.norm_eq_abs, abs_sub_comm v u, hshift]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hbound (abs_nonneg (u - v))


theorem exists_source_recent_normalized_coefficient_tolerance
    {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M]
    [IsManifold (𝓡 3) ∞ M] [T3Space M]
    {T : ℝ} (hT : 0 < T) (F : RicciFlow 3 M (Icc 0 T))
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g)
    {R v H0 : ℝ} (hR : R < N.epsilon⁻¹) (hv : v ∈ Icc 0 T) (hH0 : 0 < H0)
    (m : ℕ) (hm : m ≤ Nat.floor N.epsilon⁻¹) {nu : ℝ} (hnu : 0 < nu) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ s ∈ Icc 0 T, ∀ H : ℝ,
      |s - v| < delta → |H - H0| < delta →
      0 < H ∧ H ≤ H0 + 1 ∧ ∀ w ∈ Icc (0 : ℝ) 1,
      ∀ q : UnitTwoSphere, ∀ r ∈ Icc (-R) R, ∀ j ≤ m, ∀ a b : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y =>
          H * roundCylinderTensorCoefficient
            (roundCylinderPullback (F.metric (s * w)) N.coordinate_map) (chartAt E₂ q) y a b -
          H0 * roundCylinderTensorCoefficient
            (roundCylinderPullback (F.metric (v * w)) N.coordinate_map) (chartAt E₂ q) y a b)
            (0, r)‖ < nu := by
  obtain ⟨B, hB, hbound⟩ := neck_metric_jets_bounded_on_closed_cylinder hT F N hR m
  let L := H0 + 1
  have hL : 0 < L := by dsimp only [L]; linarith
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  let eta := min 1 (nu / (2 * (L + B + 1)))
  have heta : 0 < eta := lt_min zero_lt_one (div_pos hnu (by positivity))
  have hbudget : (L + B) * eta < nu := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * (L + B + 1))).mp
      (min_le_right (1 : ℝ) (nu / (2 * (L + B + 1))))
    change eta * (2 * (L + B + 1)) ≤ nu at h
    nlinarith only [h, heta, mul_nonneg hL.le heta.le, mul_nonneg hB0 heta.le]
  obtain ⟨dtime, hdtime, htime⟩ := neck_buffer_metric_jets_uniform_time_delta hT F N hR m hm heta
  let delta := min (H0 / 2) (min 1 (min eta dtime))
  have hdelta : 0 < delta := lt_min (half_pos hH0) (lt_min zero_lt_one (lt_min heta hdtime))
  have hdH : delta ≤ H0 / 2 := min_le_left _ _
  have hd1 : delta ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hdeta : delta ≤ eta := ((min_le_right _ _).trans (min_le_right _ _)).trans
    (min_le_left _ _)
  have hdtime : delta ≤ dtime := ((min_le_right _ _).trans (min_le_right _ _)).trans
    (min_le_right _ _)
  refine ⟨delta, hdelta, ?_⟩
  intro s hs H hsv hHH0
  have hH : 0 < H := by have h := (abs_lt.mp (hHH0.trans_le hdH)).1; linarith
  have hHL : H ≤ L := by have h := (abs_lt.mp (hHH0.trans_le hd1)).2; dsimp only [L]; linarith
  refine ⟨hH, hHL, ?_⟩
  intro w hw q r hr j hj a b
  have hsw : s * w ∈ Icc 0 T := ⟨mul_nonneg hs.1 hw.1,
    (mul_le_mul_of_nonneg_left hw.2 hs.1).trans (by simpa only [mul_one] using hs.2)⟩
  have hvw : v * w ∈ Icc 0 T := ⟨mul_nonneg hv.1 hw.1,
    (mul_le_mul_of_nonneg_left hw.2 hv.1).trans (by simpa only [mul_one] using hv.2)⟩
  have hclock : |s * w - v * w| < dtime := by
    rw [← sub_mul, abs_mul, abs_of_nonneg hw.1]
    exact ((mul_le_mul_of_nonneg_left hw.2 (abs_nonneg (s - v))).trans_eq
      (mul_one _)).trans_lt (hsv.trans_le hdtime)
  let f : V → ℝ := fun y => roundCylinderTensorCoefficient
    (roundCylinderPullback (F.metric (s * w)) N.coordinate_map) (chartAt E₂ q) y a b
  let g' : V → ℝ := fun y => roundCylinderTensorCoefficient
    (roundCylinderPullback (F.metric (v * w)) N.coordinate_map) (chartAt E₂ q) y a b
  have haxis : r ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨(neg_lt_neg hR).trans_le hr.1, hr.2.trans_lt hR⟩
  have hmem : (0, r) ∈ (chartAt E₂ q).target ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    refine ⟨?_, haxis⟩
    rw [roundCylinder_sphereChart_target]
    trivial
  have hnhds := ((chartAt E₂ q).open_target.prod isOpen_Ioo).mem_nhds hmem
  have hf : ContDiffAt ℝ ∞ f (0, r) :=
    (capPersistence_roundCylinderTensorSmoothOn_pullback
      (F.metric (s * w)) N.coordinate_map_smooth q a b).contDiffAt hnhds
  have hg : ContDiffAt ℝ ∞ g' (0, r) :=
    (capPersistence_roundCylinderTensorSmoothOn_pullback
      (F.metric (v * w)) N.coordinate_map_smooth q a b).contDiffAt hnhds
  have hid : (fun y => H * f y - H0 * g' y) =
      fun y => H • (f y - g' y) + (H - H0) • g' y := by funext y; simp only [smul_eq_mul]; ring
  change ‖iteratedFDeriv ℝ j (fun y => H * f y - H0 * g' y) (0, r)‖ < nu
  rw [hid, fun_iteratedFDeriv_add_apply
    (((hf.sub hg).const_smul H).of_le (by exact_mod_cast le_top))
    ((hg.const_smul (H - H0)).of_le (by exact_mod_cast le_top)),
    iteratedFDeriv_const_smul_apply' ((hf.sub hg).of_le (by exact_mod_cast le_top)),
    iteratedFDeriv_const_smul_apply' (hg.of_le (by exact_mod_cast le_top))]
  calc
    _ ≤ ‖H • iteratedFDeriv ℝ j (fun y => f y - g' y) (0, r)‖ +
        ‖(H - H0) • iteratedFDeriv ℝ j g' (0, r)‖ := norm_add_le _ _
    _ = H * ‖iteratedFDeriv ℝ j (fun y => f y - g' y) (0, r)‖ +
        |H - H0| * ‖iteratedFDeriv ℝ j g' (0, r)‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hH]
    _ ≤ L * eta + eta * B := add_le_add
      (mul_le_mul hHL (htime _ hsw _ hvw hclock q r hr j hj a b).le (norm_nonneg _) hL.le)
      (mul_le_mul (hHH0.trans_le hdeta).le (hbound _ hvw q r hr j hj a b)
        (norm_nonneg _) heta.le)
    _ < nu := by nlinarith only [hbudget]

end PoincareConjecture.M47
