import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.EpsilonRegularity
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.DividedDifferences

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped ContDiff Topology Manifold
namespace PoincareConjecture.M60
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m60HarmonicMap_stress_conservation (g : RiemannianMetric n M)
    {φ : LoopPlane → M} (hφ : ContMDiff (𝓡 2) (𝓡 n) ∞ φ) (p : LoopPlane)
    (hharm : let u := extChartAt (𝓡 n) (φ p) ∘ φ
      let Γ := CoordinateExponential.christoffelBilinear
        (g.pullbackCoefficients (extChartAt (𝓡 n) (φ p)).symm)
      ∑ i : Fin 2, ConnectionVariation.covDerivAlong Γ u
        (fun x => fderiv ℝ u x (EuclideanSpace.basisFun (Fin 2) ℝ i))
          (EuclideanSpace.basisFun (Fin 2) ℝ i) p = 0) :
    fderiv ℝ (fun x => m60AreaGram g φ x 0 0 - m60AreaGram g φ x 1 1) p
      (EuclideanSpace.basisFun (Fin 2) ℝ 0) =
    fderiv ℝ (fun x => -2 * m60AreaGram g φ x 0 1) p
      (EuclideanSpace.basisFun (Fin 2) ℝ 1) := by
  let c := extChartAt (𝓡 n) (φ p)
  let u := c ∘ φ
  let B := g.pullbackCoefficients c.symm
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c (φ p) := contMDiffAt_extChartAt
  have hu : ContDiffAt ℝ ∞ u p := contMDiffAt_iff_contDiffAt.mp (hc.comp p (hφ p))
  have hB : ContDiffAt ℝ ∞ B (u p) := (g.contDiffOn_chartCoefficients (φ p)).contDiffAt
    ((isOpen_extChartAt_target (φ p)).mem_nhds (c.map_source (mem_extChartAt_source _)))
  have hdu (k : Fin 2) : ContDiffAt ℝ ∞ (fun x => fderiv ℝ u x (e k)) p :=
    (hu.fderiv_right (by simp)).clm_apply contDiffAt_const
  have hcompat (v : LoopPlane) (b d : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (fun x => B (u x) b d) p v =
        B (u p) (CoordinateExponential.christoffelBilinear B (u p) (fderiv ℝ u p v) b) d +
          B (u p) b (CoordinateExponential.christoffelBilinear B (u p) (fderiv ℝ u p v) d) := by
    have hd := (((hB.differentiableAt (by simp)).hasFDerivAt.comp p
      (hu.differentiableAt (by simp)).hasFDerivAt).clm_apply
        (hasFDerivAt_const b p)).clm_apply (hasFDerivAt_const d p)
    dsimp only [Function.comp_def] at hd
    rw [hd.fderiv]
    simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      zero_apply, map_zero, zero_add]
    exact ConjugateVariation.isMetricCompatibleAt_chartCoefficients g (φ p)
      (c.map_source (mem_extChartAt_source _)) _ _ _
  have htor := ConnectionVariation.covDerivAlong_fderiv_symm
    (hu.of_le (WithTop.coe_le_coe.mpr le_top))
    (ConjugateVariation.christoffelBilinear_chart_symm g (φ p) (u p)) (e 0) (e 1)
  have h := (harmonic_pairing_cauchyRiemann
    (Γ := mapConnectionCoefficients (CoordinateExponential.christoffelBilinear B) u)
    (e 0) (e 1) ((hB.comp p hu).differentiableAt (by simp))
    ((hdu 0).differentiableAt (by simp)) ((hdu 1).differentiableAt (by simp))
    hcompat (fun _ _ => g.symm _ _ _) htor
    (by simpa only [covariantDerivative_mapConnectionCoefficients, c, u, B, e,
      Fin.sum_univ_two] using hharm)).1
  have hmem : ∀ᶠ x in 𝓝 p, φ x ∈ c.source := hφ.continuous.continuousAt.preimage_mem_nhds
    ((isOpen_extChartAt_source _).mem_nhds (mem_extChartAt_source _))
  have hpair (i j : Fin 2) :
      (fun x => B (u x) (fderiv ℝ u x (e i)) (fderiv ℝ u x (e j))) =ᶠ[𝓝 p]
        (fun x => m60AreaGram g φ x i j) := by
    filter_upwards [hmem] with x hx
    have hd (k : Fin 2) : fderiv ℝ u x (e k) = mfderiv (𝓡 n) (𝓡 n) c (φ x)
        (mfderiv (𝓡 2) (𝓡 n) φ x (e k)) := by
      have hh := mfderiv_comp x
        ((contMDiffAt_extChartAt' (x := φ p) (by simpa only [c, extChartAt_source] using hx)
          (n := ∞)).mdifferentiableAt (by simp)) ((hφ x).mdifferentiableAt (by simp))
      rw [mfderiv_eq_fderiv] at hh
      exact congrArg (fun L => L (e k)) hh
    rw [hd i, hd j]
    exact ConjugateVariation.chartCoefficients_apply g (φ p) hx _ _
  have hA := (hpair 0 0).sub (hpair 1 1)
  have hC := (EventuallyEq.refl (𝓝 p) (fun _ : LoopPlane => (-2 : ℝ))).mul (hpair 0 1)
  dsimp only [Function.comp_def] at h
  erw [hA.fderiv_eq (𝕜 := ℝ), hC.fderiv_eq (𝕜 := ℝ)] at h
  exact h

def suCylinderPoint (t θ : ℝ) : LoopPlane :=
  t • EuclideanSpace.basisFun (Fin 2) ℝ 0 + θ • EuclideanSpace.basisFun (Fin 2) ℝ 1

theorem cylinderPoint_first (t θ : ℝ) :
    HasDerivAt (fun s => suCylinderPoint s θ) (EuclideanSpace.basisFun (Fin 2) ℝ 0) t := by
  have h := ((hasDerivAt_id t).smul_const (EuclideanSpace.basisFun (Fin 2) ℝ 0)).add_const
    (θ • EuclideanSpace.basisFun (Fin 2) ℝ 1)
  simp only [one_smul, id_eq] at h
  exact h

theorem cylinderPoint_second (t θ : ℝ) :
    HasDerivAt (suCylinderPoint t) (EuclideanSpace.basisFun (Fin 2) ℝ 1) θ := by
  have h := ((hasDerivAt_id θ).smul_const (EuclideanSpace.basisFun (Fin 2) ℝ 1)).const_add
    (t • EuclideanSpace.basisFun (Fin 2) ℝ 0)
  simp only [one_smul, id_eq] at h
  exact h

theorem cylinderIntegral_hasDerivAt
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {S : LoopPlane → F}
    (hS : ContDiff ℝ ∞ S) (T t : ℝ) :
    HasDerivAt (fun s => ∫ θ in 0..T, S (suCylinderPoint s θ))
      (∫ θ in 0..T, fderiv ℝ S (suCylinderPoint t θ) (EuclideanSpace.basisFun (Fin 2) ℝ 0)) t := by
  let B := fun s θ => fderiv ℝ S (suCylinderPoint s θ) (EuclideanSpace.basisFun (Fin 2) ℝ 0)
  have hB : Continuous (Function.uncurry B) :=
    ((hS.continuous_fderiv (by simp)).comp (by dsimp only [suCylinderPoint]; fun_prop)).clm_apply
      continuous_const
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc.prod (isCompact_uIcc (a := 0) (b := T))).exists_bound_of_continuousOn
    (s := Icc (t - 1) (t + 1) ×ˢ Set.uIcc 0 T) hB.continuousOn
  have hF (s : ℝ) : Continuous (fun θ => S (suCylinderPoint s θ)) := by
    exact hS.continuous.comp
      (show Continuous (suCylinderPoint s) by unfold suCylinderPoint; fun_prop)
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := B) (s := Metric.ball t 1) (bound := fun _ => C) (Metric.ball_mem_nhds t zero_lt_one)
    (Eventually.of_forall fun s => (hF s).aestronglyMeasurable)
    ((hF t).intervalIntegrable 0 T)
    ((hB.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Eventually.of_forall fun θ hθ s hs => ?_) intervalIntegrable_const
    (Eventually.of_forall fun θ _ s _ =>
      (hS.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt s
        (cylinderPoint_first s θ))).2
  apply hC (s, θ)
  refine ⟨?_, Set.uIoc_subset_uIcc hθ⟩
  have hh := Metric.mem_ball.mp hs
  rw [Real.dist_eq, abs_lt] at hh
  constructor <;> linarith

private theorem cylinderStress_constant {S V : LoopPlane → ℝ}
    (hS : ContDiff ℝ ∞ S) (hV : ContDiff ℝ ∞ V) (T : ℝ)
    (heq : ∀ t > 0, ∀ θ : ℝ,
      fderiv ℝ S (suCylinderPoint t θ) (EuclideanSpace.basisFun (Fin 2) ℝ 0) =
        fderiv ℝ V (suCylinderPoint t θ) (EuclideanSpace.basisFun (Fin 2) ℝ 1))
    (hperiod : ∀ t > 0, V (suCylinderPoint t T) = V (suCylinderPoint t 0))
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    (∫ θ in 0..T, S (suCylinderPoint s θ)) = ∫ θ in 0..T, S (suCylinderPoint t θ) := by
  have hd (r : ℝ) (hr : 0 < r) :
      HasDerivAt (fun a => ∫ θ in 0..T, S (suCylinderPoint a θ)) 0 r := by
    have h := cylinderIntegral_hasDerivAt hS T r
    have hh : (∫ θ in 0..T, fderiv ℝ S (suCylinderPoint r θ)
        (EuclideanSpace.basisFun (Fin 2) ℝ 0)) = 0 := by
      simp_rw [heq r hr]
      have hcont : Continuous (fun θ => fderiv ℝ V (suCylinderPoint r θ)
          (EuclideanSpace.basisFun (Fin 2) ℝ 1)) :=
        ((hV.continuous_fderiv (by simp)).comp
          (show Continuous (suCylinderPoint r) by unfold suCylinderPoint; fun_prop)).clm_apply
            continuous_const
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun θ _ => (hV.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt θ
          (cylinderPoint_second r θ)) (hcont.intervalIntegrable 0 T)]
      simp only [Function.comp_apply, hperiod r hr, sub_self]
    rw [hh] at h
    exact h
  exact isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi (0 : ℝ)).isPreconnected
    (fun r hr => (hd r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hd r hr).deriv) hs ht

private theorem gram_translate (g : RiemannianMetric n M)
    {φ : LoopPlane → M} (hφ : ContMDiff (𝓡 2) (𝓡 n) ∞ φ) (a x : LoopPlane) :
    m60AreaGram g (fun y => φ (y + a)) x = m60AreaGram g φ (x + a) := by
  have hs : HasMFDerivAt (𝓡 2) (𝓡 2) (fun y : LoopPlane => y + a) x
      (ContinuousLinearMap.id ℝ LoopPlane) :=
    ((hasFDerivAt_id x).add_const a).hasMFDerivAt
  have hd := mfderiv_comp x ((hφ (x + a)).mdifferentiableAt (by simp)) hs.mdifferentiableAt
  rw [hs.mfderiv] at hd
  ext i j
  unfold m60AreaGram
  change g.inner _ (mfderiv (𝓡 2) (𝓡 n) (φ ∘ (fun y => y + a)) x _)
    (mfderiv (𝓡 2) (𝓡 n) (φ ∘ (fun y => y + a)) x _) = _
  rw [hd]
  rfl

theorem m60HarmonicCylinder_radial_angular (g : RiemannianMetric n M)
    {φ : LoopPlane → M} (hφ : ContMDiff (𝓡 2) (𝓡 n) ∞ φ) {T : ℝ} (hT : 0 < T)
    (hperiod : ∀ x, φ (x + T • EuclideanSpace.basisFun (Fin 2) ℝ 1) = φ x)
    (hharm : ∀ t > 0, ∀ θ : ℝ,
      let p := suCylinderPoint t θ
      let u := extChartAt (𝓡 n) (φ p) ∘ φ
      let Γ := CoordinateExponential.christoffelBilinear
        (g.pullbackCoefficients (extChartAt (𝓡 n) (φ p)).symm)
      ∑ i : Fin 2, ConnectionVariation.covDerivAlong Γ u
        (fun x => fderiv ℝ u x (EuclideanSpace.basisFun (Fin 2) ℝ i))
          (EuclideanSpace.basisFun (Fin 2) ℝ i) p = 0)
    (hfinite : IntegrableOn (fun t => ∫ θ in 0..T,
      2 * m60EnergyDensity g φ (suCylinderPoint t θ)) (Ioi 0)) :
    ∀ t > 0, (∫ θ in 0..T, m60AreaGram g φ (suCylinderPoint t θ) 0 0) =
      ∫ θ in 0..T, m60AreaGram g φ (suCylinderPoint t θ) 1 1 := by
  let S := fun x => m60AreaGram g φ x 0 0 - m60AreaGram g φ x 1 1
  let V := fun x => -2 * m60AreaGram g φ x 0 1
  let F := fun t => ∫ θ in 0..T, S (suCylinderPoint t θ)
  have hS : ContDiff ℝ ∞ S :=
    (m60AreaGram_entry_contDiff g hφ 0 0).sub (m60AreaGram_entry_contDiff g hφ 1 1)
  have hV : ContDiff ℝ ∞ V := contDiff_const.mul (m60AreaGram_entry_contDiff g hφ 0 1)
  have hper (t : ℝ) (_ht : 0 < t) : V (suCylinderPoint t T) = V (suCylinderPoint t 0) := by
    have he : (fun y => φ (y + T • EuclideanSpace.basisFun (Fin 2) ℝ 1)) = φ := funext hperiod
    have hg := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1)
      (gram_translate g hφ (T • EuclideanSpace.basisFun (Fin 2) ℝ 1) (suCylinderPoint t 0))
    rw [he] at hg
    dsimp only [suCylinderPoint] at hg ⊢
    simp only [zero_smul, add_zero] at hg ⊢
    dsimp only [V]
    exact congrArg (fun z : ℝ => -2 * z) hg.symm
  have hconst (t : ℝ) (ht : 0 < t) : F t = F 1 :=
    cylinderStress_constant hS hV T (fun r hr θ =>
      m60HarmonicMap_stress_conservation g hφ (suCylinderPoint r θ) (hharm r hr θ))
      hper ht zero_lt_one
  have hbound (t : ℝ) : ‖F t‖ ≤ ∫ θ in 0..T, 2 * m60EnergyDensity g φ (suCylinderPoint t θ) := by
    refine intervalIntegral.norm_integral_le_of_norm_le hT.le ?_ ?_
    · refine Eventually.of_forall fun θ _ => ?_
      have h0 := m60AreaGram_diagonal_nonneg g φ (suCylinderPoint t θ) 0
      have h1 := m60AreaGram_diagonal_nonneg g φ (suCylinderPoint t θ) 1
      change ‖_ - _‖ ≤ 2 * (1 / 2 * Matrix.trace _)
      rw [Matrix.trace_fin_two, Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · have hc := ((m60AreaGram_entry_contDiff g hφ 0 0).continuous.add
        (m60AreaGram_entry_contDiff g hφ 1 1).continuous).comp
        (show Continuous (suCylinderPoint t) by unfold suCylinderPoint; fun_prop)
      convert hc.intervalIntegrable (μ := volume) 0 T using 1
      unfold m60EnergyDensity
      simp only [Matrix.trace_fin_two, Function.comp_def, Pi.add_apply]
      funext θ; ring
  have hci : IntegrableOn (fun _ : ℝ => F 1) (Ioi 0) := hfinite.mono'
    aestronglyMeasurable_const (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [← hconst t ht]
      exact hbound t)
  have hz : F 1 = 0 := by
    rcases integrable_const_iff.mp hci with h | h
    · exact h
    · have hh := h.measure_univ_lt_top
      exfalso
      simp only [Measure.restrict_apply_univ, Real.volume_Ioi, lt_self_iff_false] at hh
  intro t ht
  have he : F t = 0 := (hconst t ht).trans hz
  have hi (i : Fin 2) : IntervalIntegrable
      (fun θ => m60AreaGram g φ (suCylinderPoint t θ) i i) volume 0 T :=
    ((m60AreaGram_entry_contDiff g hφ i i).continuous.comp
      (show Continuous (suCylinderPoint t) by unfold suCylinderPoint; fun_prop)).intervalIntegrable
        0 T
  rw [show F t = (∫ θ in 0..T, m60AreaGram g φ (suCylinderPoint t θ) 0 0) -
    (∫ θ in 0..T, m60AreaGram g φ (suCylinderPoint t θ) 1 1) from
      intervalIntegral.integral_sub (hi 0) (hi 1)] at he
  exact sub_eq_zero.mp he

private theorem intervalIntegral_square_bound {v : ℝ → ℝ} (hv : Continuous v)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ θ in 0..T, v θ) ^ 2 ≤ T * (∫ θ in 0..T, (v θ) ^ 2) := by
  let I := ∫ θ in 0..T, v θ
  let J := ∫ θ in 0..T, (v θ) ^ 2
  have hi := hv.intervalIntegrable (μ := volume) 0 T
  have hj := (hv.pow 2).intervalIntegrable (μ := volume) 0 T
  have hpoly (a : ℝ) : 0 ≤ T * (a * a) + (2 * I) * a + J := by
    have h := intervalIntegral.integral_nonneg (μ := volume) hT
      (fun θ _ => sq_nonneg (v θ + a))
    have he : (fun θ => (v θ + a) ^ 2) =
        (fun θ => ((v θ) ^ 2 + (2 * a) * v θ) + a ^ 2) := by funext θ; ring
    rw [he] at h
    erw [intervalIntegral.integral_add (hj.add (hi.const_mul _)) intervalIntegrable_const,
      intervalIntegral.integral_add hj (hi.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const] at h
    simp only [sub_zero, smul_eq_mul] at h
    change 0 ≤ J + (2 * a) * I + T * a ^ 2 at h
    nlinarith only [h]
  have hd := discrim_le_zero hpoly
  unfold discrim at hd
  change I ^ 2 ≤ T * J
  nlinarith only [hd]

theorem circleMean_poincare
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {u : ℝ → F} (hu : ContDiff ℝ ∞ u) {T : ℝ} (hT : 0 < T) {θ : ℝ}
    (hθ : θ ∈ Icc 0 T) :
    ‖u θ - T⁻¹ • (∫ s in 0..T, u s)‖ ^ 2 ≤
      4 * T * (∫ s in 0..T, ‖deriv u s‖ ^ 2) := by
  let I := ∫ s in 0..T, ‖deriv u s‖
  have hv : Continuous (fun s => ‖deriv u s‖) := (hu.continuous_deriv (by simp)).norm
  have hI : 0 ≤ I := intervalIntegral.integral_nonneg hT.le (fun _ _ => norm_nonneg _)
  have hdisp (r : ℝ) (hr : r ∈ Icc 0 T) : ‖u r - u 0‖ ≤ I := by
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => (hu.differentiable (by simp) s).hasDerivAt)
      ((hu.continuous_deriv (by simp)).intervalIntegrable (μ := volume) 0 r)
    rw [← he]
    exact (intervalIntegral.norm_integral_le_integral_norm hr.1).trans
      (intervalIntegral.integral_mono_interval le_rfl hr.1 hr.2
        (Eventually.of_forall fun _ => norm_nonneg _) (hv.intervalIntegrable 0 T))
  have hmean : u θ - T⁻¹ • (∫ s in 0..T, u s) =
      T⁻¹ • (∫ s in 0..T, u θ - u s) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      (hu.continuous.intervalIntegrable 0 T), intervalIntegral.integral_const, sub_zero,
      smul_sub, inv_smul_smul₀ hT.ne']
  have hb : ‖∫ s in 0..T, u θ - u s‖ ≤ (2 * I) * T := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := T)
      (f := fun s => u θ - u s) (C := 2 * I) (fun s hs => ?_)
    · simpa only [sub_zero, abs_of_pos hT] using h
    · have hs' : s ∈ Icc 0 T := by
        rw [Set.uIoc_of_le hT.le] at hs
        exact ⟨hs.1.le, hs.2⟩
      have htri := norm_sub_le_norm_sub_add_norm_sub (u θ) (u 0) (u s)
      rw [norm_sub_rev (u 0) (u s)] at htri
      exact htri.trans (by linarith [hdisp θ hθ, hdisp s hs'])
  have hn : ‖u θ - T⁻¹ • (∫ s in 0..T, u s)‖ ≤ 2 * I := by
    rw [hmean, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hT)]
    calc
      _ ≤ T⁻¹ * ((2 * I) * T) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hT.le)
      _ = 2 * I := by field_simp
  have hs := mul_self_le_mul_self (norm_nonneg _) hn
  have hc := intervalIntegral_square_bound hv hT.le
  change I ^ 2 ≤ T * (∫ s in 0..T, ‖deriv u s‖ ^ 2) at hc
  nlinarith only [hs, hc]

def cylinderMean {k : ℕ} (u : LoopPlane → EuclideanSpace ℝ (Fin k)) (T t : ℝ) :=
  T⁻¹ • (∫ θ in 0..T, u (suCylinderPoint t θ))

theorem cylinderMean_contDiff {k : ℕ} {u : LoopPlane → EuclideanSpace ℝ (Fin k)}
    (hu : ContDiff ℝ ∞ u) (T : ℝ) : ContDiff ℝ ∞ (cylinderMean u T) := by
  have hp : ContDiff ℝ ∞ (fun x : ℝ × ℝ => suCylinderPoint x.1 x.2) := by
    unfold suCylinderPoint; fun_prop
  exact (contDiff_const (c := T⁻¹)).smul
    (Poincare.Analysis.contDiff_parameter_intervalIntegral_of_contDiff (hu.comp hp) 0 T)

theorem cylinderMean_hasDerivAt {k : ℕ} {u : LoopPlane → EuclideanSpace ℝ (Fin k)}
    (hu : ContDiff ℝ ∞ u) (T t : ℝ) :
    HasDerivAt (cylinderMean u T)
      (cylinderMean (fun x => fderiv ℝ u x (EuclideanSpace.basisFun (Fin 2) ℝ 0)) T t) t :=
  (cylinderIntegral_hasDerivAt hu T t).const_smul T⁻¹

def cylinderColumn {k : ℕ} (u : LoopPlane → EuclideanSpace ℝ (Fin k))
    (i : Fin 2) (x : LoopPlane) := fderiv ℝ u x (EuclideanSpace.basisFun (Fin 2) ℝ i)

theorem cylinderColumn_contDiff {k : ℕ} {u : LoopPlane → EuclideanSpace ℝ (Fin k)}
    (hu : ContDiff ℝ ∞ u) (i : Fin 2) : ContDiff ℝ ∞ (cylinderColumn u i) :=
  (hu.fderiv_right (by simp)).clm_apply contDiff_const

def cylinderCentered {k : ℕ} (u : LoopPlane → EuclideanSpace ℝ (Fin k))
    (T : ℝ) (x : LoopPlane) := u x - cylinderMean u T (x 0)

theorem cylinderPoint_zero (t θ : ℝ) : suCylinderPoint t θ 0 = t := by
  simp [suCylinderPoint, EuclideanSpace.basisFun_apply]

theorem cylinderCentered_contDiff {k : ℕ} {u : LoopPlane → EuclideanSpace ℝ (Fin k)}
    (hu : ContDiff ℝ ∞ u) (T : ℝ) : ContDiff ℝ ∞ (cylinderCentered u T) := by
  have hc : ContDiff ℝ ∞ (fun x : LoopPlane => x 0) := by fun_prop
  exact hu.sub ((cylinderMean_contDiff hu T).comp hc)

theorem cylinderCentered_integral {k : ℕ} {u : LoopPlane → EuclideanSpace ℝ (Fin k)}
    (hu : ContDiff ℝ ∞ u) {T : ℝ} (hT : 0 < T) (t : ℝ) :
    (∫ θ in 0..T, cylinderCentered u T (suCylinderPoint t θ)) = 0 := by
  have hi : IntervalIntegrable (fun θ => u (suCylinderPoint t θ)) volume 0 T :=
    (hu.continuous.comp (show Continuous (suCylinderPoint t) by
      unfold suCylinderPoint; fun_prop)).intervalIntegrable 0 T
  simp only [cylinderCentered, cylinderPoint_zero, cylinderMean]
  rw [intervalIntegral.integral_sub hi intervalIntegrable_const, intervalIntegral.integral_const,
    sub_zero, smul_smul, mul_inv_cancel₀ hT.ne', one_smul, sub_self]

theorem cylinderCentered_first {k : ℕ} {u : LoopPlane → EuclideanSpace ℝ (Fin k)}
    (hu : ContDiff ℝ ∞ u) (T t θ : ℝ) :
    HasDerivAt (fun s => cylinderCentered u T (suCylinderPoint s θ))
      (cylinderCentered (cylinderColumn u 0) T (suCylinderPoint t θ)) t := by
  have h := ((hu.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
    (cylinderPoint_first t θ)).sub (cylinderMean_hasDerivAt hu T t)
  simp only [cylinderCentered, cylinderPoint_zero, cylinderColumn]
  simp only [Function.comp_def] at h
  exact h

theorem cylinderCentered_second {k : ℕ} {u : LoopPlane → EuclideanSpace ℝ (Fin k)}
    (hu : ContDiff ℝ ∞ u) (T t θ : ℝ) :
    HasDerivAt (fun s => cylinderCentered u T (suCylinderPoint t s))
      (cylinderColumn u 1 (suCylinderPoint t θ)) θ := by
  have h := ((hu.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt θ
    (cylinderPoint_second t θ)).sub_const (cylinderMean u T t)
  simpa only [Function.comp_def, cylinderCentered, cylinderPoint_zero, cylinderColumn] using h

private theorem cylinder_angular_integration {k : ℕ}
    {u : LoopPlane → EuclideanSpace ℝ (Fin k)} (hu : ContDiff ℝ ∞ u) (T t : ℝ)
    (hperiod : ∀ x, u (x + T • EuclideanSpace.basisFun (Fin 2) ℝ 1) = u x) :
    (∫ θ in 0..T, ‖cylinderColumn u 1 (suCylinderPoint t θ)‖ ^ 2 +
      inner ℝ (cylinderCentered u T (suCylinderPoint t θ))
        (cylinderColumn (cylinderColumn u 1) 1 (suCylinderPoint t θ))) = 0 := by
  let Z := cylinderColumn u 1
  let w := cylinderCentered u T
  have hZ := cylinderColumn_contDiff hu 1
  have hZ1 := cylinderColumn_contDiff hZ 1
  have hw := cylinderCentered_contDiff hu T
  have hd (θ : ℝ) : HasDerivAt
      (fun s => inner ℝ (w (suCylinderPoint t s)) (Z (suCylinderPoint t s)))
      (‖Z (suCylinderPoint t θ)‖ ^ 2 + inner ℝ (w (suCylinderPoint t θ))
        (cylinderColumn Z 1 (suCylinderPoint t θ))) θ := by
    have h := (cylinderCentered_second hu T t θ).inner ℝ
      ((hZ.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt θ (cylinderPoint_second t θ))
    simp only [Function.comp_def, real_inner_self_eq_norm_sq, add_comm] at h
    exact h
  have hcont : Continuous (fun θ => ‖Z (suCylinderPoint t θ)‖ ^ 2 +
      inner ℝ (w (suCylinderPoint t θ)) (cylinderColumn Z 1 (suCylinderPoint t θ))) :=
    ((hZ.continuous.norm.pow 2).add (hw.continuous.inner hZ1.continuous)).comp
      (show Continuous (suCylinderPoint t) by unfold suCylinderPoint; fun_prop)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hd θ)
    (hcont.intervalIntegrable 0 T)]
  have hpoint : suCylinderPoint t T = suCylinderPoint t 0 +
      T • EuclideanSpace.basisFun (Fin 2) ℝ 1 := by simp [suCylinderPoint]
  have hwp : w (suCylinderPoint t T) = w (suCylinderPoint t 0) := by
    simp only [w, cylinderCentered, cylinderPoint_zero]
    rw [hpoint, hperiod]
  have hzp : Z (suCylinderPoint t T) = Z (suCylinderPoint t 0) := by
    have hf := congrArg (fun f : LoopPlane → EuclideanSpace ℝ (Fin k) =>
      fderiv ℝ f (suCylinderPoint t 0)) (funext hperiod)
    rw [fderiv_comp_add_right] at hf
    rw [hpoint]
    exact congrArg (fun L => L (EuclideanSpace.basisFun (Fin 2) ℝ 1)) hf
  rw [hwp, hzp, sub_self]

theorem cylinderRadialComparison_hasDerivAt {k : ℕ}
    {u : LoopPlane → EuclideanSpace ℝ (Fin k)} (hu : ContDiff ℝ ∞ u)
    {T : ℝ} (hT : 0 < T) (t : ℝ)
    (hperiod : ∀ x, u (x + T • EuclideanSpace.basisFun (Fin 2) ℝ 1) = u x) :
    HasDerivAt
      (fun s => ∫ θ in 0..T, inner ℝ (cylinderCentered u T (suCylinderPoint s θ))
        (cylinderColumn u 0 (suCylinderPoint s θ)))
      (∫ θ in 0..T,
        ‖cylinderCentered (cylinderColumn u 0) T (suCylinderPoint t θ)‖ ^ 2 +
        ‖cylinderColumn u 1 (suCylinderPoint t θ)‖ ^ 2 +
        inner ℝ (cylinderCentered u T (suCylinderPoint t θ))
          (cylinderColumn (cylinderColumn u 0) 0 (suCylinderPoint t θ) +
            cylinderColumn (cylinderColumn u 1) 1 (suCylinderPoint t θ))) t := by
  let Y := cylinderColumn u 0
  let Z := cylinderColumn u 1
  let w := cylinderCentered u T
  let v := cylinderCentered Y T
  let S := fun x => inner ℝ (w x) (Y x)
  let A := fun x => ‖Z x‖ ^ 2 + inner ℝ (w x) (cylinderColumn Z 1 x)
  let B := fun x => inner ℝ (cylinderMean Y T t) (v x)
  let D := fun x => ‖v x‖ ^ 2 + ‖Z x‖ ^ 2 +
    inner ℝ (w x) (cylinderColumn Y 0 x + cylinderColumn Z 1 x)
  have hY := cylinderColumn_contDiff hu 0
  have hZ := cylinderColumn_contDiff hu 1
  have hw := cylinderCentered_contDiff hu T
  have hv := cylinderCentered_contDiff hY T
  have hY0 := cylinderColumn_contDiff hY 0
  have hZ1 := cylinderColumn_contDiff hZ 1
  have hS : ContDiff ℝ ∞ S := hw.inner ℝ hY
  have hp : Continuous (suCylinderPoint t) := by unfold suCylinderPoint; fun_prop
  have hA : IntervalIntegrable (fun θ => A (suCylinderPoint t θ)) volume 0 T :=
    (((hZ.continuous.norm.pow 2).add (hw.continuous.inner hZ1.continuous)).comp
      hp).intervalIntegrable 0 T
  have hB : IntervalIntegrable (fun θ => B (suCylinderPoint t θ)) volume 0 T :=
    ((continuous_const.inner hv.continuous).comp hp).intervalIntegrable 0 T
  have hD : IntervalIntegrable (fun θ => D (suCylinderPoint t θ)) volume 0 T :=
    ((((hv.continuous.norm.pow 2).add (hZ.continuous.norm.pow 2)).add
      (hw.continuous.inner (hY0.continuous.add hZ1.continuous))).comp hp).intervalIntegrable 0 T
  have hAz : (∫ θ in 0..T, A (suCylinderPoint t θ)) = 0 :=
    cylinder_angular_integration hu T t hperiod
  have hBz : (∫ θ in 0..T, B (suCylinderPoint t θ)) = 0 := by
    have hh := (innerSL ℝ (cylinderMean Y T t)).intervalIntegral_comp_comm
      ((hv.continuous.comp hp).intervalIntegrable (μ := volume) 0 T)
    simp only [Function.comp_def] at hh
    rw [cylinderCentered_integral hY hT t, map_zero] at hh
    exact hh
  have hd (θ : ℝ) : fderiv ℝ S (suCylinderPoint t θ)
      (EuclideanSpace.basisFun (Fin 2) ℝ 0) =
        D (suCylinderPoint t θ) - A (suCylinderPoint t θ) + B (suCylinderPoint t θ) := by
    have h1 := (hS.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
      (cylinderPoint_first t θ)
    have h2 := (cylinderCentered_first hu T t θ).inner ℝ
      ((hY.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t (cylinderPoint_first t θ))
    have he := h1.unique h2
    simp only [Function.comp_def] at he
    rw [he]
    change inner ℝ (w (suCylinderPoint t θ)) (cylinderColumn Y 0 (suCylinderPoint t θ)) +
      inner ℝ (v (suCylinderPoint t θ)) (Y (suCylinderPoint t θ)) = _
    have hy : Y (suCylinderPoint t θ) = v (suCylinderPoint t θ) + cylinderMean Y T t := by
      simp [v, cylinderCentered, cylinderPoint_zero]
    rw [hy, inner_add_right, real_inner_self_eq_norm_sq]
    dsimp only [D, A, B]
    rw [inner_add_right, real_inner_comm (v (suCylinderPoint t θ)) (cylinderMean Y T t)]
    ring
  have h := cylinderIntegral_hasDerivAt hS T t
  have he : (∫ θ in 0..T, fderiv ℝ S (suCylinderPoint t θ)
      (EuclideanSpace.basisFun (Fin 2) ℝ 0)) = ∫ θ in 0..T, D (suCylinderPoint t θ) := by
    simp_rw [hd]
    rw [intervalIntegral.integral_add (hD.sub hA) hB,
      intervalIntegral.integral_sub hD hA, hAz, hBz, sub_zero, add_zero]
  rw [he] at h
  exact h

theorem cylinderRadialComparison_bound {k : ℕ}
    {u : LoopPlane → EuclideanSpace ℝ (Fin k)} (hu : ContDiff ℝ ∞ u)
    {T : ℝ} (hT : 0 < T) (t : ℝ) :
    |∫ θ in 0..T, inner ℝ (cylinderCentered u T (suCylinderPoint t θ))
        (cylinderColumn u 0 (suCylinderPoint t θ))| ≤
      T * (∫ θ in 0..T, ‖cylinderColumn u 0 (suCylinderPoint t θ)‖ ^ 2 +
        ‖cylinderColumn u 1 (suCylinderPoint t θ)‖ ^ 2) := by
  let Y := cylinderColumn u 0
  let Z := cylinderColumn u 1
  let w := cylinderCentered u T
  let J := ∫ θ in 0..T, ‖Z (suCylinderPoint t θ)‖ ^ 2
  have hp : ContDiff ℝ ∞ (suCylinderPoint t) := by unfold suCylinderPoint; fun_prop
  have hY := cylinderColumn_contDiff hu 0
  have hZ := cylinderColumn_contDiff hu 1
  have hw := cylinderCentered_contDiff hu T
  have hder (θ : ℝ) : deriv (u ∘ suCylinderPoint t) θ = Z (suCylinderPoint t θ) := by
    exact ((hu.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt θ
      (cylinderPoint_second t θ)).deriv
  have hwbound (θ : ℝ) (hθ : θ ∈ Icc 0 T) : ‖w (suCylinderPoint t θ)‖ ^ 2 ≤ 4 * T * J := by
    have h := circleMean_poincare (hu.comp hp) hT hθ
    simp_rw [hder] at h
    simpa only [w, cylinderCentered, cylinderMean, cylinderPoint_zero, Function.comp_def] using h
  have hpoint (θ : ℝ) (hθ : θ ∈ Icc 0 T) :
      |inner ℝ (w (suCylinderPoint t θ)) (Y (suCylinderPoint t θ))| ≤
        J + T * ‖Y (suCylinderPoint t θ)‖ ^ 2 := by
    have hc := abs_real_inner_le_norm (w (suCylinderPoint t θ)) (Y (suCylinderPoint t θ))
    have hs := sq_nonneg (‖w (suCylinderPoint t θ)‖ - 2 * T * ‖Y (suCylinderPoint t θ)‖)
    have hh := hwbound θ hθ
    have hb : 4 * T * (‖w (suCylinderPoint t θ)‖ * ‖Y (suCylinderPoint t θ)‖) ≤
        4 * T * (J + T * ‖Y (suCylinderPoint t θ)‖ ^ 2) := by
      nlinarith only [hs, hh]
    exact hc.trans ((mul_le_mul_iff_right₀ (by positivity : 0 < 4 * T)).mp hb)
  have hIi : IntervalIntegrable (fun θ =>
      |inner ℝ (w (suCylinderPoint t θ)) (Y (suCylinderPoint t θ))|) volume 0 T :=
    (((hw.continuous.inner hY.continuous).comp hp.continuous).abs).intervalIntegrable 0 T
  have hYi := ((hY.continuous.norm.pow 2).comp hp.continuous).intervalIntegrable
    (μ := volume) 0 T
  have hZi := ((hZ.continuous.norm.pow 2).comp hp.continuous).intervalIntegrable
    (μ := volume) 0 T
  calc
    _ ≤ ∫ θ in 0..T, |inner ℝ (w (suCylinderPoint t θ)) (Y (suCylinderPoint t θ))| :=
      intervalIntegral.abs_integral_le_integral_abs hT.le
    _ ≤ ∫ θ in 0..T, J + T * ‖Y (suCylinderPoint t θ)‖ ^ 2 :=
      intervalIntegral.integral_mono_on hT.le hIi
        (intervalIntegrable_const.add (hYi.const_mul T)) hpoint
    _ = T * (∫ θ in 0..T, ‖Y (suCylinderPoint t θ)‖ ^ 2 +
        ‖Z (suCylinderPoint t θ)‖ ^ 2) := by
      erw [intervalIntegral.integral_add intervalIntegrable_const (hYi.const_mul T),
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add hYi hZi]
      simp only [sub_zero, smul_eq_mul, J, Z, Function.comp_def, Pi.pow_apply]
      ring

end PoincareConjecture.M60
