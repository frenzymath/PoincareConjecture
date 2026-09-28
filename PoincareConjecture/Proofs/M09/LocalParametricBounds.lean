import PoincareConjecture.Proofs.M09.ParametricChartDerivatives
import PoincareConjecture.Proofs.M09.UniformPositiveForm
import PoincareConjecture.Definitions.Ch06.ReducedLength








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology BigOperators
open Filter

universe u v

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P] {J : Set ℝ}

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
theorem exists_local_parametric_derivative_bounds (F : RicciFlow n M J) (T τmax : ℝ)
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J) (p : M)
    (C : (P × E) × ℝ → ℝ) (U : Set ((P × E) × ℝ))
    (hU : IsOpen U) (hC : ContDiffOn ℝ ∞ C U)
    (z0 : (P × E) × ℝ) (hz0 : z0 ∈ U)
    (hy0 : z0.1.2 ∈ (chartAt E p).target) (ht0 : 0 < z0.2) (hmax0 : z0.2 < τmax) :
    ∃ W : Set ((P × E) × ℝ), IsOpen W ∧ z0 ∈ W ∧
      W ⊆ U ∩ ((Set.univ ×ˢ (chartAt E p).target) ×ˢ Set.Ioo 0 τmax) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ W,
        let q := (chartAt E p).symm z.1.2
        let f : M × ℝ → ℝ := fun w ↦ C ((z.1.1, (chartAt E p) w.1), w.2)
        |deriv (fun s ↦ f (q, s)) z.2| ≤ B ∧
        reducedLengthGradientNormSq F T f z.2 q ≤ B ∧
        ∀ v : TangentSpace (𝓡 n) q,
          (F.connection (T - z.2)).hessian (fun x ↦ f (x, z.2)) q v v ≤
            B * (F.metric (T - z.2)).inner q v v := by
  classical
  let e := chartAt E p
  let S := U ∩ ((Set.univ ×ˢ e.target) ×ˢ Set.Ioo 0 τmax)
  have hS : IsOpen S := hU.inter ((isOpen_univ.prod e.open_target).prod isOpen_Ioo)
  have hzS : z0 ∈ S := ⟨hz0, ⟨Set.mem_univ _, hy0⟩, ht0, hmax0⟩
  let G : (P × E) × ℝ → E →L[ℝ] E →L[ℝ] ℝ :=
    fun z ↦ squareChartMetric F T p (Real.sqrt z.2, z.1.2)
  let L := parametricSpatialCovector C
  let H := parametricChartHessian F T p C
  let d : (P × E) × ℝ → ℝ := fun z ↦ fderiv ℝ C z ((0, 0), 1)
  have hG : ContDiffOn ℝ ∞ G S :=
    (squareChartMetric_smooth F T τmax hτmax hwindow p).comp
      ((contDiffOn_snd.sqrt (fun z hz ↦ hz.2.2.1.ne')).prodMk
        contDiff_fst.snd.contDiffOn) (fun z hz ↦
          ⟨⟨(neg_neg_of_pos (Real.sqrt_pos.mpr hτmax)).trans_le (Real.sqrt_nonneg _),
            Real.sqrt_lt_sqrt hz.2.2.1.le hz.2.2.2⟩, hz.2.1.2⟩)
  have hL := (parametricSpatialCovector_smooth C U hU hC).contDiffAt (hU.mem_nhds hz0)
  have hH := (parametricChartHessian_smooth F T τmax hτmax hwindow p C U hU hC).contDiffAt
    (hS.mem_nhds hzS)
  have hd : ContDiffAt ℝ ∞ d z0 :=
    ((hC.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const).contDiffAt
      (hU.mem_nhds hz0)
  obtain ⟨c, hc, V, hV, hzV, hcoercive⟩ := exists_uniform_positiveForm_lower_bound
    G z0 ((hG.contDiffAt (hS.mem_nhds hzS)).continuousAt)
      (fun u hu ↦ squareChartMetric_pos F T p (Real.sqrt z0.2, z0.1.2) hy0 u hu)
  let D := max ‖L z0‖ (max ‖H z0‖ |d z0|) + 1
  have hD : 0 ≤ D := by
    have := le_max_left ‖L z0‖ (max ‖H z0‖ |d z0|)
    have := norm_nonneg (L z0)
    dsimp only [D]
    linarith
  have hLD : ‖L z0‖ < D := lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)
  have hHD : ‖H z0‖ < D := lt_of_le_of_lt
    ((le_max_left _ _).trans (le_max_right _ _)) (lt_add_one _)
  have hdD : |d z0| < D := lt_of_le_of_lt
    ((le_max_right _ _).trans (le_max_right _ _)) (lt_add_one _)
  have hnear : ∀ᶠ z in 𝓝 z0,
      z ∈ S ∧ z ∈ V ∧ ‖L z‖ ≤ D ∧ ‖H z‖ ≤ D ∧ |d z| ≤ D := by
    filter_upwards [hS.mem_nhds hzS, hV.mem_nhds hzV,
      hL.continuousAt.norm.eventually (isOpen_Iio.mem_nhds hLD),
      hH.continuousAt.norm.eventually (isOpen_Iio.mem_nhds hHD),
      hd.continuousAt.abs.eventually (isOpen_Iio.mem_nhds hdD)] with z hz hzV hLz hHz hdz
    exact ⟨hz, hzV, hLz.le, hHz.le, hdz.le⟩
  obtain ⟨W, hWsub, hW, hzW⟩ := mem_nhds_iff.mp hnear
  let B := max D (max ((n : ℝ) * D ^ 2 / c) (D / c))
  have hDB : D ≤ B := le_max_left _ _
  have hGB : (n : ℝ) * D ^ 2 / c ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hHB : D / c ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨W, hW, hzW, fun z hz ↦ (hWsub hz).1, B, hD.trans hDB, ?_⟩
  intro z hz
  obtain ⟨hzS, hzV, hLz, hHz, hdz⟩ := hWsub hz
  let q := e.symm z.1.2
  let f : M × ℝ → ℝ := fun w ↦ C ((z.1.1, e w.1), w.2)
  have hy := hzS.2.1.2
  have ht := hzS.2.2.1
  obtain ⟨hfirst, hsecond, htime⟩ := parametric_chart_derivatives F T τmax hτmax hwindow
    p C U hU hC z.1.1 z.1.2 z.2 hy ht hzS.2.2.2 hzS.1
  have hmetric (u : E) : G z u u = (F.metric (T - z.2)).inner q
      (chartVectorField p u q) (chartVectorField p u q) := by
    rw [chartVectorField_at_inverse p u z.1.2 hy]
    change (F.metric (T - (Real.sqrt z.2) ^ 2)).inner q _ _ = _
    rw [Real.sq_sqrt ht.le]
    rfl
  have hcovector (v : TangentSpace (𝓡 n) q) :
      (mvfderiv (𝓡 n) (fun x ↦ f (x, z.2)) q v) ^ 2 ≤
        (D ^ 2 / c) * (F.metric (T - z.2)).inner q v v := by
    obtain ⟨u, hu⟩ := (inverseChartDifferential_bijective p z.1.2 hy).2 v
    have hu' : chartVectorField p u q = v :=
      (chartVectorField_at_inverse p u z.1.2 hy).trans hu
    rw [← hu', hfirst, ← hmetric]
    exact covector_sq_le_positiveForm (G z) c D hc hD (hcoercive z hzV) (L z) hLz u
  have hhessian (v : TangentSpace (𝓡 n) q) :
      (F.connection (T - z.2)).hessian (fun x ↦ f (x, z.2)) q v v ≤
        (D / c) * (F.metric (T - z.2)).inner q v v := by
    obtain ⟨u, hu⟩ := (inverseChartDifferential_bijective p z.1.2 hy).2 v
    have hu' : chartVectorField p u q = v :=
      (chartVectorField_at_inverse p u z.1.2 hy).trans hu
    rw [← hu', hsecond, ← hmetric]
    exact bilinear_le_positiveForm (G z) c D hc hD (hcoercive z hzV) (H z) hHz u
  refine ⟨?_, ?_, ?_⟩
  · have htime' : deriv (fun s ↦ f (q, s)) z.2 = d z := htime
    exact (by rwa [htime'] : |deriv (fun s ↦ f (q, s)) z.2| ≤ D).trans hDB
  · letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric (T - z.2)).toRiemannianMetric⟩
    let b := (F.metric (T - z.2)).orthonormalBasis q
    have hb (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) q))) :
        (F.metric (T - z.2)).inner q (b i) (b i) = 1 := by
      change inner ℝ (b i) (b i) = 1
      simp
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) q) = n := by
      change Module.finrank ℝ E = n
      simp
    apply le_trans _ hGB
    calc
      reducedLengthGradientNormSq F T f z.2 q ≤
          ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) q)), D ^ 2 / c := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [hb i, mul_one] using hcovector (b i)
      _ = (n : ℝ) * D ^ 2 / c := by simp [hdim, mul_div_assoc]
  · intro v
    have hv : 0 ≤ (F.metric (T - z.2)).inner q v v := by
      rcases eq_or_ne v 0 with rfl | hne
      · simp
      · exact ((F.metric (T - z.2)).pos q v hne).le
    exact (hhessian v).trans (mul_le_mul_of_nonneg_right hHB hv)

end PoincareConjecture.Proofs.M09
