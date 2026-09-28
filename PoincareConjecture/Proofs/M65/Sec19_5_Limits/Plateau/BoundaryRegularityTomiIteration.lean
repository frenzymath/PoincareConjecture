import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityTomi
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityLocalCutoff










set_option autoImplicit false

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff SchwartzMap LineDeriv InnerProductSpace

namespace PoincareConjecture.M65Boundary

open EuclideanTranslationNative EuclideanDerivativeNative DeTurckDomainRegularityNative
  DeTurckHigherDomainNative DeTurckGeneratorRegularityNative

private theorem centered_weak_pair
    (u : ScalarL2 2) (d : Fin 2 → ScalarL2 2) (c : ℝ) (θ : 𝓢(LoopPlane, ℝ))
    (hw : ∀ i (φ : 𝓢(LoopPlane, ℝ)),
      ⟪d i, φ.toLp 2 volume⟫_ℝ =
        -(∫ z, u z * fderiv ℝ φ z (EuclideanSpace.single i 1))) :
    ∃ (w : ScalarL2 2) (dw : Fin 2 → ScalarL2 2),
      (∀ᵐ z ∂volume, w z = u z - c * θ z) ∧
      (∀ i, ∀ᵐ z ∂volume,
        dw i z = d i z - c * fderiv ℝ θ z (EuclideanSpace.single i 1)) ∧
      (∀ i (φ : 𝓢(LoopPlane, ℝ)),
        ⟪dw i, φ.toLp 2 volume⟫_ℝ =
          -(∫ z, w z * fderiv ℝ φ z (EuclideanSpace.single i 1))) ∧
      ‖w‖ ≤ ‖u‖ + |c| * ‖θ.toLp 2 volume‖ ∧
      (∀ i, ‖dw i‖ ≤ ‖d i‖ + |c| *
        ‖(∂_{EuclideanSpace.single i (1 : ℝ)} θ).toLp 2 volume‖) := by
  let w := u - c • θ.toLp 2 volume
  let dw := fun i : Fin 2 => d i - c • (∂_{EuclideanSpace.single i (1 : ℝ)} θ).toLp 2 volume
  have hθweak (i : Fin 2) : HasWeakSchwartzDerivative (θ.toLp 2 volume)
      ((∂_{EuclideanSpace.single i (1 : ℝ)} θ).toLp 2 volume)
      (EuclideanSpace.single i 1) := by
    intro φ
    rw [inner_schwartz, inner_schwartz]
    have hleft : (∫ z, (∂_{EuclideanSpace.single i (1 : ℝ)} θ).toLp 2 volume z * φ z) =
        ∫ z, fderiv ℝ θ z (EuclideanSpace.single i 1) * φ z := by
      apply integral_congr_ae
      filter_upwards [(∂_{EuclideanSpace.single i (1 : ℝ)} θ).coeFn_toLp 2 volume]
        with z hz
      rw [hz]
      rfl
    have hright : (∫ z, θ.toLp 2 volume z * (∂_{EuclideanSpace.single i (1 : ℝ)} φ) z) =
        ∫ z, θ z * fderiv ℝ φ z (EuclideanSpace.single i 1) := by
      apply integral_congr_ae
      filter_upwards [θ.coeFn_toLp 2 volume] with z hz
      rw [hz]
      rfl
    rw [hleft, hright]
    have hh := SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left θ φ
      (EuclideanSpace.single i (1 : ℝ)) (μ := volume)
    simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv] at hh
    linarith only [hh]
  refine ⟨w, dw, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_sub u (c • θ.toLp 2 volume),
      Lp.coeFn_smul c (θ.toLp 2 volume), θ.coeFn_toLp 2 volume] with z hz hs hθ
    rw [hz, Pi.sub_apply, hs, Pi.smul_apply, smul_eq_mul, hθ]
  · intro i
    filter_upwards [Lp.coeFn_sub (d i)
      (c • (∂_{EuclideanSpace.single i (1 : ℝ)} θ).toLp 2 volume),
      Lp.coeFn_smul c ((∂_{EuclideanSpace.single i (1 : ℝ)} θ).toLp 2 volume),
      (∂_{EuclideanSpace.single i (1 : ℝ)} θ).coeFn_toLp 2 volume]
      with z hz hs hθ
    rw [hz, Pi.sub_apply, hs, Pi.smul_apply, smul_eq_mul, hθ]
    rfl
  · intro i φ
    have hh : HasWeakSchwartzDerivative w (dw i) (EuclideanSpace.single i 1) := by
      intro ψ
      have huψ := hasWeakSchwartzDerivative_of_integral u (d i)
        (EuclideanSpace.single i 1) (hw i) ψ
      have hθψ := hθweak i ψ
      simp only [w, dw, inner_sub_left, real_inner_smul_left]
      rw [huψ, hθψ]
      ring
    simpa only [inner_schwartz, SchwartzMap.lineDerivOp_apply_eq_fderiv] using hh φ
  · exact (norm_sub_le _ _).trans (by rw [norm_smul, Real.norm_eq_abs])
  · intro i
    exact (norm_sub_le _ _).trans (by rw [norm_smul, Real.norm_eq_abs])

private theorem centered_equation
    (d dw : Fin 2 → ScalarL2 2) (f : LoopPlane → ℝ) {U : Set LoopPlane}
    (hU : IsOpen U) (hd : ∀ i, d i =ᵐ[volume.restrict U] dw i)
    (heq : ∀ φ : 𝓢(LoopPlane, ℝ), HasCompactSupport φ → tsupport φ ⊆ U →
      (∑ i : Fin 2, ⟪d i, (∂_{EuclideanSpace.single i (1 : ℝ)} φ).toLp 2 volume⟫_ℝ) =
        -(∫ z, f z * φ z)) :
    ∀ φ : 𝓢(LoopPlane, ℝ), HasCompactSupport φ → tsupport φ ⊆ U →
      (∑ i : Fin 2, ⟪dw i, (∂_{EuclideanSpace.single i (1 : ℝ)} φ).toLp 2 volume⟫_ℝ) =
        -(∫ z, f z * φ z) := by
  intro φ hc hs
  rw [← heq φ hc hs]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_schwartz, inner_schwartz]
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' hU.measurableSet).mp (hd i)] with z hz
  by_cases hzU : z ∈ U
  · rw [hz hzU]
  · have hzero : (∂_{EuclideanSpace.single i (1 : ℝ)} φ) z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hzU (hs
        (SchwartzMap.tsupport_lineDerivOp_subset (EuclideanSpace.single i 1) φ h)))
    rw [hzero, mul_zero, mul_zero]

private theorem weighted_gradient_global {N : ℕ} {b ρ : ℝ}
    (hb : 1 < b) (hρ : 0 < ρ) :
    ∃ K ≥ 0, ∀ (d : Fin N → Fin 2 → ScalarL2 2) (x : LoopPlane)
      (U : Set LoopPlane), MeasurableSet U → closedBall x ρ ⊆ U →
      IntegrableOn (fun z => ‖z - x‖ ^ (-b) *
        (∑ j : Fin N, ∑ i : Fin 2, |d j i z|)) U →
      Integrable (fun z => ‖z - x‖ ^ (-b) *
        (∑ j : Fin N, ∑ i : Fin 2, |d j i z|)) ∧
      (∫ z, ‖z - x‖ ^ (-b) * (∑ j : Fin N, ∑ i : Fin 2, |d j i z|)) ≤
        (∫ z in U, ‖z - x‖ ^ (-b) * (∑ j : Fin N, ∑ i : Fin 2, |d j i z|)) +
        (∑ j : Fin N, ∑ i : Fin 2, (K + ‖d j i‖ ^ 2)) := by
  obtain ⟨K, hK, htail⟩ := weighted_gradient_tail hb hρ
  refine ⟨K, hK, ?_⟩
  intro d x U hU hball hlocal
  let T := (closedBall x ρ)ᶜ
  let G := fun z => ‖z - x‖ ^ (-b) * (∑ j : Fin N, ∑ i : Fin 2, |d j i z|)
  have hti : IntegrableOn G T := by
    simp_rw [G, Finset.mul_sum]
    exact integrable_finsetSum _ fun j _ =>
      integrable_finsetSum _ fun i _ => (htail x (d j i)).1
  have htc : Uᶜ ⊆ T := compl_subset_compl.mpr hball
  have hglobal : Integrable G := by
    have hi := integrableOn_union.mpr ⟨hlocal, hti.mono_set htc⟩
    simpa only [union_compl_self, integrableOn_univ] using hi
  refine ⟨hglobal, ?_⟩
  rw [← integral_add_compl hU hglobal]
  apply add_le_add le_rfl
  calc
    (∫ z in Uᶜ, G z) ≤ ∫ z in T, G z :=
      setIntegral_mono_set hti (ae_of_all _ fun z => by dsimp only [G]; positivity)
        htc.eventuallyLE
    _ = ∑ j : Fin N, ∑ i : Fin 2,
        ∫ z in T, ‖z - x‖ ^ (-b) * |d j i z| := by
      simp_rw [G, Finset.mul_sum]
      rw [integral_finsetSum _ fun j _ =>
        integrable_finsetSum _ fun i _ => (htail x (d j i)).1]
      apply Finset.sum_congr rfl
      intro j _
      exact integral_finsetSum _ fun i _ => (htail x (d j i)).1
    _ ≤ _ := Finset.sum_le_sum fun j _ =>
      Finset.sum_le_sum fun i _ => (htail x (d j i)).2

set_option maxHeartbeats 1600000 in





theorem centered_weighted_energy_step {N : ℕ} (u : Fin N → ScalarL2 2)
    (d : Fin N → Fin 2 → ScalarL2 2) (f : Fin N → LoopPlane → ℝ)
    (hf : ∀ j, Integrable (f j)) {U : Set LoopPlane} (hU : IsOpen U)
    (hweak : ∀ j i (φ : 𝓢(LoopPlane, ℝ)),
      ⟪d j i, φ.toLp 2 volume⟫_ℝ =
        -(∫ z, u j z * fderiv ℝ φ z (EuclideanSpace.single i 1)))
    (heq : ∀ j (φ : 𝓢(LoopPlane, ℝ)), HasCompactSupport φ → tsupport φ ⊆ U →
      (∑ i : Fin 2, ⟪d j i, (∂_{EuclideanSpace.single i (1 : ℝ)} φ).toLp 2 volume⟫_ℝ) =
        -(∫ z, f j z * φ z))
    (θ : 𝓢(LoopPlane, ℝ)) (hθ : ∀ z ∈ U, θ z = 1 ∧ fderiv ℝ θ z = 0)
    {B C H α β ρ : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H) (hα : 0 ≤ α)
    (hρ : 0 < ρ) (hb : 1 < α + 1 - β)
    (hbound : ∀ j, ∀ᵐ z ∂volume, ‖u j z‖ ≤ B)
    (χ : 𝓢(LoopPlane, ℝ)) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ U)
    (hχ : ∀ z, |χ z| ≤ 1) :
    ∃ K ≥ 0, ∀ (x : LoopPlane) (c : Fin N → ℝ),
      (∀ j, |c j| ≤ C) → closedBall x ρ ⊆ U →
      (∀ᵐ z ∂volume, z ∈ U →
        |∑ j : Fin N, f j z * (u j z - c j)| ≤
          (∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2) / 2) →
      (∀ j, ∀ᵐ z ∂volume, z ∈ U → |u j z - c j| ≤ H * ‖z - x‖ ^ β) →
      (∀ z, ‖z - x‖ < ρ → ∀ i : Fin 2,
        fderiv ℝ χ z (EuclideanSpace.single i 1) = 0) →
      IntegrableOn (fun z => ‖z - x‖ ^ (-(α + 1 - β)) *
        (∑ j : Fin N, ∑ i : Fin 2, |d j i z|)) U →
      Integrable (fun z => χ z ^ 2 * ‖z - x‖ ^ (-α) *
        (∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2)) ∧
      (∫ z, χ z ^ 2 * ‖z - x‖ ^ (-α) *
        (∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2)) ≤
        K + 4 * α * H * ∫ z in U, ‖z - x‖ ^ (-(α + 1 - β)) *
          (∑ j : Fin N, ∑ i : Fin 2, |d j i z|) := by
  classical
  obtain ⟨K0, hK0, hglobal⟩ := weighted_gradient_global (N := N) hb hρ
  let W := fun j : Fin N => ‖u j‖ + C * ‖θ.toLp 2 volume‖
  let D := fun j i => ‖d j i‖ + C *
    ‖(∂_{EuclideanSpace.single i (1 : ℝ)} θ).toLp 2 volume‖
  let S := ∑ j : Fin N, ∑ i : Fin 2,
    (‖schwartzMultiplier (∂_{EuclideanSpace.single i (1 : ℝ)} χ)‖ * W j) ^ 2
  let T := ∑ j : Fin N, ∑ i : Fin 2, (K0 + D j i ^ 2)
  let K := 16 * ρ ^ (-α) * S + 4 * α * H * T
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hT : 0 ≤ T := Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => add_nonneg hK0 (sq_nonneg _)
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  intro x c hcC hball hsmall hholder hflat hJ
  choose w dw hwv hdv hwg hwn hdn using
    fun j => centered_weak_pair (u j) (d j) (c j) θ (hweak j)
  have hwU : ∀ᵐ z ∂volume, z ∈ U → ∀ j, w j z = u j z - c j := by
    filter_upwards [ae_all_iff.mpr hwv] with z hz hzU j
    rw [hz j, (hθ z hzU).1, mul_one]
  have hdU : ∀ᵐ z ∂volume, z ∈ U → ∀ j i, dw j i z = d j i z := by
    filter_upwards [ae_all_iff.mpr (fun j => ae_all_iff.mpr (hdv j))] with z hz hzU j i
    rw [hz j i, (hθ z hzU).2, zero_apply, mul_zero, sub_zero]
  have hdlocal (j : Fin N) (i : Fin 2) : d j i =ᵐ[volume.restrict U] dw j i := by
    apply (ae_restrict_iff' hU.measurableSet).mpr
    filter_upwards [hdU] with z hz hzU
    exact (hz hzU j i).symm
  have hwbound (j : Fin N) : ∀ᵐ z ∂volume,
      ‖w j z‖ ≤ B + C * SchwartzMap.seminorm ℝ 0 0 θ := by
    filter_upwards [hwv j, hbound j] with z hz hu
    rw [hz]
    calc
      ‖u j z - c j * θ z‖ ≤ ‖u j z‖ + |c j| * ‖θ z‖ := by
        simpa only [norm_mul, Real.norm_eq_abs] using norm_sub_le (u j z) (c j * θ z)
      _ ≤ _ := add_le_add hu (mul_le_mul (hcC j) (θ.norm_le_seminorm ℝ z)
        (norm_nonneg _) hC)
  have hwsmall : ∀ᵐ z ∂volume, z ∈ U →
      |∑ j : Fin N, f j z * w j z| ≤
        (∑ j : Fin N, ∑ i : Fin 2, (dw j i z) ^ 2) / 2 := by
    filter_upwards [hwU, hdU, hsmall] with z hwz hdz hsz hzU
    simpa only [hwz hzU, hdz hzU] using hsz hzU
  have hwholder (j : Fin N) : ∀ᵐ z ∂volume, z ∈ U →
      |w j z| ≤ H * ‖z - x‖ ^ β := by
    filter_upwards [hwU, hholder j] with z hwz hz hzU
    simpa only [hwz hzU j] using hz hzU
  have hJlocal : IntegrableOn (fun z => ‖z - x‖ ^ (-(α + 1 - β)) *
      (∑ j : Fin N, ∑ i : Fin 2, |dw j i z|)) U := by
    apply hJ.congr
    filter_upwards [ae_restrict_mem hU.measurableSet, hdU.filter_mono ae_restrict_le]
      with z hzU hdz
    simp only [hdz hzU]
  obtain ⟨hJglobal, hJbound⟩ := hglobal dw x U hU.measurableSet hball hJlocal
  have hJint : (∫ z in U, ‖z - x‖ ^ (-(α + 1 - β)) *
      (∑ j : Fin N, ∑ i : Fin 2, |dw j i z|)) =
        ∫ z in U, ‖z - x‖ ^ (-(α + 1 - β)) *
          (∑ j : Fin N, ∑ i : Fin 2, |d j i z|) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hU.measurableSet, hdU.filter_mono ae_restrict_le]
      with z hzU hdz
    simp only [hdz hzU]
  have hwnorm (j : Fin N) : ‖w j‖ ≤ W j :=
    (hwn j).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right (hcC j) (norm_nonneg _)))
  have hdnorm (j : Fin N) (i : Fin 2) : ‖dw j i‖ ≤ D j i :=
    (hdn j i).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right (hcC j) (norm_nonneg _)))
  have hJestimate : (∫ z, ‖z - x‖ ^ (-(α + 1 - β)) *
      (∑ j : Fin N, ∑ i : Fin 2, |dw j i z|)) ≤
        (∫ z in U, ‖z - x‖ ^ (-(α + 1 - β)) *
          (∑ j : Fin N, ∑ i : Fin 2, |d j i z|)) + T := by
    rw [hJint] at hJbound
    exact hJbound.trans (add_le_add le_rfl (Finset.sum_le_sum fun j _ =>
      Finset.sum_le_sum fun i _ => add_le_add le_rfl
        (pow_le_pow_left₀ (norm_nonneg _) (hdnorm j i) 2)))
  have hSbound : (∑ j : Fin N, ∑ i : Fin 2,
      ‖schwartzMultiplier (∂_{EuclideanSpace.single i (1 : ℝ)} χ) (w j)‖ ^ 2) ≤ S := by
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro i _
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    exact ((schwartzMultiplier _).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hwnorm j) (norm_nonneg _))
  obtain ⟨hEi, hEb⟩ := weighted_energy_step w dw f hf hU hwg
    (fun j => centered_equation (d j) (dw j) (f j) hU (hdlocal j) (heq j))
    hwbound hwsmall x hH hα hρ hwholder χ hc hs hχ hflat hJglobal
  have hEeq : (fun z => χ z ^ 2 * ‖z - x‖ ^ (-α) *
      (∑ j : Fin N, ∑ i : Fin 2, (dw j i z) ^ 2)) =ᵐ[volume]
        (fun z => χ z ^ 2 * ‖z - x‖ ^ (-α) *
          (∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2)) := by
    filter_upwards [hdU] with z hz
    by_cases hzU : z ∈ U
    · simp only [hz hzU]
    · have hzero : χ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hzU (hs h))
      simp only [hzero, zero_pow (by norm_num : 2 ≠ 0), zero_mul]
  refine ⟨hEi.congr hEeq, ?_⟩
  rw [← integral_congr_ae hEeq]
  refine hEb.trans ?_
  have hprod := add_le_add
    (mul_le_mul_of_nonneg_left hSbound (by positivity : 0 ≤ 16 * ρ ^ (-α)))
    (mul_le_mul_of_nonneg_left hJestimate (by positivity : 0 ≤ 4 * α * H))
  exact hprod.trans_eq (by dsimp only [K]; ring)

end PoincareConjecture.M65Boundary
