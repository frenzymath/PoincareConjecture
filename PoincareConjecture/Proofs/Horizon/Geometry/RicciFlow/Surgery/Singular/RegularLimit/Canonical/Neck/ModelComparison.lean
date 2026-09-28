import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.ModelParallel
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.Comparison



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators InnerProductSpace

noncomputable section

namespace PoincareConjecture.SingularRegularLimit

theorem cylinderWeight_pos {u : ℝ} (hu : u < 1)
    (p : RoundCylinderCoordinates) (i : Fin 3) : 0 < cylinderWeight u p i := by
  have hs := sphereFactor_pos p
  have h : 0 < (2 * (1 - u) * sphereFactor p)⁻¹ := by positivity
  fin_cases i
  · exact h
  · exact h
  · exact zero_lt_one

theorem cylinderNorm_smul {u : ℝ} (hu : u ≠ 1) (q : UnitTwoSphere)
    (p : RoundCylinderCoordinates) {r : ℕ} (A : (Fin r → Fin 3) → ℝ) (c : ℝ) :
    roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p
        (fun a => c * A a) =
      c ^ 2 * roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p A := by
  rw [cylinderNorm_diagonal hu, cylinderNorm_diagonal hu, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem cylinderNorm_add_le {u : ℝ} (hu : u < 1) (q : UnitTwoSphere)
    (p : RoundCylinderCoordinates) {r : ℕ} (A B : (Fin r → Fin 3) → ℝ) :
    roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p
        (fun a => A a + B a) ≤
      2 * roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p A +
        2 * roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p B := by
  rw [cylinderNorm_diagonal hu.ne, cylinderNorm_diagonal hu.ne,
    cylinderNorm_diagonal hu.ne, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  have hw : 0 ≤ ∏ i, cylinderWeight u p (a i) :=
    Finset.prod_nonneg (fun i _ => (cylinderWeight_pos hu p (a i)).le)
  calc
    _ ≤ (∏ i, cylinderWeight u p (a i)) * (2 * (A a) ^ 2 + 2 * (B a) ^ 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (A a - B a)]) hw
    _ = _ := by ring

theorem cylinderParallelCoefficient_norm {u : ℝ} (hu : u ≠ 1)
    (q : UnitTwoSphere) (p : RoundCylinderCoordinates) (A B : ℝ) :
    roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p
        (fun a : Fin 2 → Fin 3 => cylinderParallelCoefficient A B p (a 0) (a 1)) =
      2 * (A / (2 * (1 - u))) ^ 2 + B ^ 2 := by
  have hu' : 1 - u ≠ 0 := sub_ne_zero.mpr hu.symm
  have hp : sphereFactor p ≠ 0 := (sphereFactor_pos p).ne'
  rw [cylinderNorm_diagonal hu]
  have heq := Fintype.sum_equiv (finTwoArrowEquiv (Fin 3))
    (fun a : Fin 2 → Fin 3 => (∏ i, cylinderWeight u p (a i)) *
      (cylinderParallelCoefficient A B p (a 0) (a 1)) ^ 2)
    (fun a : Fin 3 × Fin 3 => cylinderWeight u p a.1 * cylinderWeight u p a.2 *
      (cylinderParallelCoefficient A B p a.1 a.2) ^ 2)
    (fun _ => by simp [Fin.prod_univ_two])
  rw [heq, Fintype.sum_prod_type]
  simp [Fin.sum_univ_three, cylinderWeight, cylinderParallelCoefficient,
    roundCylinderCoordinateBasis, EuclideanSpace.inner_single_left]
  field_simp
  ring



theorem cylinder_scaled_model_jetError {u : ℝ} (hu : u ≠ 1)
    (v c : ℝ) (order : ℕ) (z : RoundCylinderSpace) :
    roundCylinderJetErrorSquared u
        (fun z x y => c * EvolvingRoundCylinderMetric v z x y) order z =
      2 * ((c * (1 - v) - (1 - u)) / (1 - u)) ^ 2 + (c - 1) ^ 2 := by
  have hu' : 1 - u ≠ 0 := sub_ne_zero.mpr hu.symm
  unfold roundCylinderJetErrorSquared
  rw [Finset.sum_eq_single 0]
  · have heq := funext (roundCylinder_scaled_model_zeroth u v c z.1
      ((chartAt (EuclideanSpace ℝ (Fin 2)) z.1) z.1, z.2))
    rw [heq, cylinderParallelCoefficient_norm hu]
    field_simp
  · intro k _ hk
    rcases k with _ | k
    · exact (hk rfl).elim
    · have heq := funext (roundCylinder_scaled_model_positive_jet_zero hu v c z.1 k
        ((chartAt (EuclideanSpace ℝ (Fin 2)) z.1) z.1, z.2))
      rw [heq]
      simp [roundCylinderTensorNormSquared]
  · simp

theorem cylinder_covariant_component_smoothAt {ε u : ℝ} (hu : u < 1)
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderTensorSmoothOn ε B)
    (q : UnitTwoSphere) (k : ℕ) (p : RoundCylinderCoordinates)
    (hp : p.2 ∈ Ioo (-ε⁻¹) ε⁻¹) (a : Fin (2 + k) → Fin 3) :
    ContDiffAt ℝ ∞ (fun r => roundCylinderIteratedDerivative u
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) B k r a) p := by
  induction k with
  | zero =>
      have hb := hB q (a 0) (a 1)
      rw [roundCylinder_sphereChart_target] at hb
      exact (hb.contDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds
        ⟨mem_univ _, hp⟩)).sub (contDiff_roundCylinderGram u q (a 0) (a 1)).contDiffAt
  | succ k ih =>
      simp only [roundCylinderIteratedDerivative, roundCylinderTensorDerivative]
      apply ContDiffAt.sub
      · exact ((ih _).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
      · apply ContDiffAt.sum
        intro i _
        apply ContDiffAt.sum
        intro j _
        exact (contDiff_roundCylinderChristoffel hu q j (a 0) (a i.succ)).contDiffAt.mul (ih _)

theorem scaled_cylinder_model_smooth (ε v c : ℝ) :
    RoundCylinderTensorSmoothOn ε (fun z x y => c * EvolvingRoundCylinderMetric v z x y) := by
  intro q i j
  exact (contDiff_const.mul (contDiff_roundCylinderGram v q i j)).contDiffOn



theorem cylinder_covariant_scaled_error {ε u v : ℝ} (hu : u < 1) (hv : v < 1)
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderTensorSmoothOn ε B)
    (c : ℝ) (q : UnitTwoSphere) (k : ℕ) (p : RoundCylinderCoordinates)
    (hp : p.2 ∈ Ioo (-ε⁻¹) ε⁻¹) (a : Fin (2 + k) → Fin 3) :
    roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (fun z x y => c * B z x y) k p a =
      c * roundCylinderIteratedDerivative v (chartAt (EuclideanSpace ℝ (Fin 2)) q) B k p a +
        roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
          (fun z x y => c * EvolvingRoundCylinderMetric v z x y) k p a := by
  induction k generalizing p with
  | zero =>
      simp only [roundCylinderIteratedDerivative, roundCylinderTensorCoefficient,
        roundCylinderGram]
      ring
  | succ k ih =>
      have hΓ : roundCylinderChristoffel u (chartAt (EuclideanSpace ℝ (Fin 2)) q) =
          roundCylinderChristoffel v (chartAt (EuclideanSpace ℝ (Fin 2)) q) :=
        (roundCylinderChristoffel_time_eq hu.ne q).trans
          (roundCylinderChristoffel_time_eq hv.ne q).symm
      have heq : (fun r => roundCylinderIteratedDerivative u
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) (fun z x y => c * B z x y) k r
            (fun i => a i.succ)) =ᶠ[𝓝 p]
          (fun r => c * roundCylinderIteratedDerivative v
            (chartAt (EuclideanSpace ℝ (Fin 2)) q) B k r (fun i => a i.succ) +
            roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
              (fun z x y => c * EvolvingRoundCylinderMetric v z x y) k r (fun i => a i.succ)) := by
        filter_upwards [(isOpen_univ.prod isOpen_Ioo).mem_nhds
          (show p ∈ (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹ : Set RoundCylinderCoordinates) from
            ⟨mem_univ _, hp⟩)] with r hr
        exact ih r hr.2 _
      have h₁ := (cylinder_covariant_component_smoothAt hv hB q k p hp
        (fun i => a i.succ)).differentiableAt (by simp)
      have h₂ := (cylinder_covariant_component_smoothAt hu
        (scaled_cylinder_model_smooth ε v c) q k p hp
        (fun i => a i.succ)).differentiableAt (by simp)
      simp only [roundCylinderIteratedDerivative, roundCylinderTensorDerivative]
      erw [heq.fderiv_eq (𝕜 := ℝ)]
      erw [fderiv_add (h₁.const_mul c) h₂, fderiv_const_mul h₁ c]
      simp only [add_apply, smul_apply, smul_eq_mul]
      simp_rw [ih p hp, hΓ]
      simp only [mul_add, Finset.sum_add_distrib, ← mul_assoc]
      ring_nf
      simp only [Finset.mul_sum, mul_assoc]
      ring!




theorem cylinder_scaled_jetError_le {ε u v : ℝ} (huv : u ≤ v) (hv : v < 1)
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderTensorSmoothOn ε B)
    (c : ℝ) (order : ℕ) (z : RoundCylinderSpace)
    (hz : z.2 ∈ Ioo (-ε⁻¹) ε⁻¹) :
    roundCylinderJetErrorSquared u (fun z x y => c * B z x y) order z ≤
      2 * c ^ 2 * roundCylinderJetErrorSquared v B order z +
        2 * roundCylinderJetErrorSquared u
          (fun z x y => c * EvolvingRoundCylinderMetric v z x y) order z := by
  have hu : u < 1 := huv.trans_lt hv
  unfold roundCylinderJetErrorSquared
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  let q := chartAt (EuclideanSpace ℝ (Fin 2)) z.1
  let p : RoundCylinderCoordinates := (q z.1, z.2)
  have heq : roundCylinderIteratedDerivative u q (fun z x y => c * B z x y) k p =
      fun a => c * roundCylinderIteratedDerivative v q B k p a +
        roundCylinderIteratedDerivative u q
          (fun z x y => c * EvolvingRoundCylinderMetric v z x y) k p a := by
    funext a
    exact cylinder_covariant_scaled_error hu hv hB c z.1 k p hz a
  change roundCylinderTensorNormSquared u q p _ ≤ _
  rw [heq]
  apply (cylinderNorm_add_le hu z.1 p _ _).trans
  rw [cylinderNorm_smul hu.ne]
  apply add_le_add _ le_rfl
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (roundCylinderTensorNormSquared_time_mono huv hv z.1 p
      (roundCylinderIteratedDerivative v q B k p))
    (show 0 ≤ 2 * c ^ 2 by positivity)

theorem cylinder_scaled_jetError_le_explicit {ε u v : ℝ} (huv : u ≤ v) (hv : v < 1)
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderTensorSmoothOn ε B)
    (c : ℝ) (order : ℕ) (z : RoundCylinderSpace)
    (hz : z.2 ∈ Ioo (-ε⁻¹) ε⁻¹) :
    roundCylinderJetErrorSquared u (fun z x y => c * B z x y) order z ≤
      2 * c ^ 2 * roundCylinderJetErrorSquared v B order z +
        4 * ((c * (1 - v) - (1 - u)) / (1 - u)) ^ 2 + 2 * (c - 1) ^ 2 := by
  have h := cylinder_scaled_jetError_le huv hv hB c order z hz
  rw [cylinder_scaled_model_jetError (huv.trans_lt hv).ne] at h
  convert h using 1
  ring




theorem roundCylinderFamilyClose_retained_clock {ε c d : ℝ}
    (hε : 0 < ε) (hc : 1 ≤ c) (hcmax : c ≤ 6 / 5)
    (hcε : c - 1 ≤ ε / 4) (hd : 0 ≤ d) (hdε : d ≤ ε / 4)
    {B : ℝ → RoundCylinderTwoTensor}
    (hB : RoundCylinderFamilyClose ε (Ioc (-1 : ℝ) 0) B) :
    RoundCylinderFamilyClose (2 * ε) (Ioc (-1 : ℝ) 0 ∩ Iic (-d))
      (fun s z x y => c * B ((d + s) / c) z x y) := by
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hweak : ε ≤ 2 * ε := by linarith
  have hclock (s : ℝ) (hs : s ∈ Ioc (-1 : ℝ) 0 ∩ Iic (-d)) :
      (d + s) / c ∈ Ioc (-1 : ℝ) 0 ∧ s ≤ (d + s) / c := by
    have hcut : s ≤ -d := hs.2
    refine ⟨⟨(lt_div_iff₀ hcpos).2 (by nlinarith [hs.1.1]),
      (div_le_iff₀ hcpos).2 (by nlinarith)⟩,
      (le_div_iff₀ hcpos).2 ?_⟩
    have hprod : s * (c - 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hs.1.2 (by linarith)
    nlinarith
  obtain ⟨hsmooth, bound, hbound, hjet⟩ := hB
  refine ⟨?_, (7 / 2 : ℝ) * ε ^ 2, by nlinarith [sq_pos_of_pos hε], ?_⟩
  · intro s hs q i j
    exact (contDiffOn_const.mul (hsmooth _ (hclock s hs).1 q i j)).mono
      (Set.prod_mono subset_rfl (DeepHorn.neckInterval_subset hε hweak))
  · intro s hs z hz
    let v := (d + s) / c
    have hv : v ∈ Ioc (-1 : ℝ) 0 := (hclock s hs).1
    have hsv : s ≤ v := (hclock s hs).2
    have hz' := DeepHorn.neckInterval_subset hε hweak hz
    have horder : ⌊(2 * ε)⁻¹⌋₊ ≤ ⌊ε⁻¹⌋₊ :=
      Nat.floor_mono ((inv_le_inv₀ (by positivity) hε).2 hweak)
    have hold : roundCylinderJetErrorSquared v (B v) ⌊(2 * ε)⁻¹⌋₊ z ≤ ε ^ 2 :=
      (DeepHorn.evolvingCylinderJetErrorSquared_mono (hv.2.trans_lt (by norm_num))
        (B v) z horder).trans ((hjet v hv z hz').trans hbound.le)
    have hestimate := cylinder_scaled_jetError_le_explicit hsv
      (hv.2.trans_lt (by norm_num)) (hsmooth v hv) c ⌊(2 * ε)⁻¹⌋₊ z hz'
    have hden : 0 < 1 - s := by linarith [hs.1.2]
    have hnum : c * (1 - v) - (1 - s) = c - 1 - d := by
      dsimp [v]
      field_simp
      ring
    have hnumabs : |c - 1 - d| ≤ ε / 4 := by
      apply abs_le.mpr
      constructor <;> linarith
    have hratio : |(c * (1 - v) - (1 - s)) / (1 - s)| ≤ ε / 4 := by
      rw [hnum, abs_div, abs_of_pos hden]
      apply (div_le_iff₀ hden).2
      nlinarith [hs.1.2]
    have hratio2 : ((c * (1 - v) - (1 - s)) / (1 - s)) ^ 2 ≤ (ε / 4) ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) (show 0 ≤ ε / 4 by positivity)).2 hratio
    have hc2 : c ^ 2 ≤ (36 / 25 : ℝ) := by nlinarith
    have hscale := mul_le_mul_of_nonneg_right hc2 (sq_nonneg ε)
    have hsmall : (c - 1) ^ 2 ≤ (ε / 4) ^ 2 := by nlinarith
    have hold' := mul_le_mul_of_nonneg_left hold (show 0 ≤ 2 * c ^ 2 by positivity)
    nlinarith

end PoincareConjecture.SingularRegularLimit
