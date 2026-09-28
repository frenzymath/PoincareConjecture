import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.EpsilonRegularityCylinder
import PoincareConjecture.Proofs.Horizon.Topology.VectorBundle.CompactDisk
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompactHessian
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Hessian.Chart
import PoincareConjecture.Proofs.M60.Mathlib.SecondDerivativeChain
import PoincareConjecture.Proofs.Horizon.Analysis.ODE.ScalarComparison
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUAlphaEnergy

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ContDiff Topology Manifold

namespace PoincareConjecture.M60

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

open scoped Bundle in

theorem suEmbedding_differential_lower_bound [CompactSpace M] [T2Space M]
    (g : RiemannianMetric n M) {k : ℕ} (e : M → EuclideanSpace ℝ (Fin k))
    (he : ContMDiff (𝓡 n) (𝓡 k) ∞ e)
    (hi : ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 k) e x)) :
    ∃ c : ℝ, 0 < c ∧ ∀ x (v : TangentSpace (𝓡 n) x),
      c * g.inner x v v ≤ ‖(show EuclideanSpace ℝ (Fin k) from
        mfderiv (𝓡 n) (𝓡 k) e x v)‖ ^ 2 := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let S : Set (TangentBundle (𝓡 n) M) := {v | v.1 ∈ (univ : Set M) ∧ ‖v.2‖ = 1}
  let F : TangentBundle (𝓡 n) M → ℝ := fun v =>
    ‖(show EuclideanSpace ℝ (Fin k) from mfderiv (𝓡 n) (𝓡 k) e v.1 v.2)‖ ^ 2
  have hS : IsCompact S := Poincare.VectorBundle.isCompact_sphere_over isCompact_univ 1
  have hF : Continuous F := by
    have h := ((tangentBundleModelSpaceHomeomorph (𝓡 k)).continuous.comp
      (he.continuous_tangentMap (by simp))).snd.norm.pow 2
    exact h
  have hpos (v : TangentBundle (𝓡 n) M) (hv : v ∈ S) : 0 < F v := by
    apply sq_pos_of_pos
    apply norm_pos_iff.mpr
    intro hzero
    have hz : v.2 = 0 := hi v.1 (by simpa only [map_zero] using hzero)
    have hn := hv.2
    rw [hz, norm_zero] at hn
    norm_num at hn
  let K := F '' S ∪ {1}
  have hK : IsCompact K := (hS.image hF).union isCompact_singleton
  obtain ⟨c, hc, hcmin⟩ := hK.exists_isMinOn ⟨1, Or.inr (mem_singleton 1)⟩
    continuous_id.continuousOn
  have hcpos : 0 < c := by
    rcases hc with ⟨v, hv, rfl⟩ | hc
    · exact hpos v hv
    · simpa only [mem_singleton_iff] using hc ▸ (show (0 : ℝ) < 1 by norm_num)
  refine ⟨c, hcpos, fun x v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hunit : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvp), inv_mul_cancel₀ hvp.ne']
  have hb : c ≤ F ⟨x, (‖v‖⁻¹ : ℝ) • v⟩ :=
    hcmin (Or.inl ⟨⟨x, (‖v‖⁻¹ : ℝ) • v⟩, ⟨mem_univ x, hunit⟩, rfl⟩)
  dsimp only [F] at hb
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvp), mul_pow,
    inv_pow] at hb
  have h := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖v‖)
  rw [mul_assoc, mul_comm (‖(show EuclideanSpace ℝ (Fin k) from
      mfderiv (𝓡 n) (𝓡 k) e x v)‖ ^ 2),
    ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hvp.ne'), one_mul] at h
  have hn : g.inner x v v = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
  rw [hn]
  exact h

private theorem harmonic_composition_laplacian {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {s : M → ℝ} (hs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ s)
    {φ : LoopPlane → M} (hφ : ContMDiff (𝓡 2) (𝓡 n) ∞ φ) (p : LoopPlane)
    (hharm : let u := extChartAt (𝓡 n) (φ p) ∘ φ
      let Γ := CoordinateExponential.christoffelBilinear
        (g.pullbackCoefficients (extChartAt (𝓡 n) (φ p)).symm)
      ∑ i : Fin 2, ConnectionVariation.covDerivAlong Γ u
        (fun x => fderiv ℝ u x (EuclideanSpace.basisFun (Fin 2) ℝ i))
          (EuclideanSpace.basisFun (Fin 2) ℝ i) p = 0) :
    (∑ i : Fin 2, fderiv ℝ (fderiv ℝ (s ∘ φ)) p (EuclideanSpace.basisFun (Fin 2) ℝ i)
      (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
    ∑ i : Fin 2, D.hessian s (φ p)
      (mfderiv (𝓡 2) (𝓡 n) φ p (EuclideanSpace.basisFun (Fin 2) ℝ i))
      (mfderiv (𝓡 2) (𝓡 n) φ p (EuclideanSpace.basisFun (Fin 2) ℝ i)) := by
  let c := extChartAt (𝓡 n) (φ p)
  let u := c ∘ φ
  let r := s ∘ c.symm
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let Γ := CoordinateExponential.christoffelBilinear (g.pullbackCoefficients c.symm)
  have hx : u p ∈ c.target := c.map_source (mem_extChartAt_source _)
  have hcu : c.symm (u p) = φ p := c.left_inv (mem_extChartAt_source _)
  have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c (φ p) := contMDiffAt_extChartAt
  have hcs : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm (u p) :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) (φ p) hx).contMDiffAt
      (extChartAt_target_mem_nhds' hx)
  have hu : ContDiffAt ℝ 2 u p :=
    (contMDiffAt_iff_contDiffAt.mp (hc.comp p (hφ p))).of_le (WithTop.coe_le_coe.mpr le_top)
  have hr : ContDiffAt ℝ 2 r (u p) :=
    (contMDiffAt_iff_contDiffAt.mp ((hs _).comp _ hcs)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hdu : fderiv ℝ u p = mfderiv (𝓡 2) (𝓡 n) φ p := by
    rw [← mfderiv_eq_fderiv]
    change mfderiv (𝓡 2) (𝓡 n) (c ∘ φ) p = _
    rw [mfderiv_comp p (hc.mdifferentiableAt (by simp)) ((hφ p).mdifferentiableAt (by simp))]
    change (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) (φ p)) (φ p)).comp _ = _
    rw [mfderiv_extChartAt_self, ContinuousLinearMap.id_comp]
  have hci : mfderiv (𝓡 n) (𝓡 n) c.symm (u p) = ContinuousLinearMap.id ℝ _ := by
    have h := mfderivWithin_range_extChartAt_symm (I := 𝓡 n) (x := φ p)
    simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at h
    exact h
  have hH (i : Fin 2) : D.hessian s (φ p) (fderiv ℝ u p (e i)) (fderiv ℝ u p (e i)) =
      fderiv ℝ (fderiv ℝ r) (u p) (fderiv ℝ u p (e i)) (fderiv ℝ u p (e i)) -
        fderiv ℝ r (u p) (Γ (u p) (fderiv ℝ u p (e i)) (fderiv ℝ u p (e i))) := by
    have hh := D.hessian_in_chart (φ p) hx (hs _) (fderiv ℝ u p (e i)) (fderiv ℝ u p (e i))
    change D.hessian s (c.symm (u p))
      (mfderiv (𝓡 n) (𝓡 n) c.symm (u p) (fderiv ℝ u p (e i)))
      (mfderiv (𝓡 n) (𝓡 n) c.symm (u p) (fderiv ℝ u p (e i))) = _ at hh
    rw [hci] at hh
    change D.hessian s (c.symm (u p)) (fderiv ℝ u p (e i)) (fderiv ℝ u p (e i)) = _ at hh
    rw [hcu] at hh
    exact hh
  have hmem : ∀ᶠ x in 𝓝 p, φ x ∈ c.source := hφ.continuous.continuousAt.preimage_mem_nhds
    ((isOpen_extChartAt_source _).mem_nhds (mem_extChartAt_source _))
  have heq : r ∘ u =ᶠ[𝓝 p] s ∘ φ := by
    filter_upwards [hmem] with x hx
    exact congrArg s (c.left_inv hx)
  have ht : (fderiv ℝ (fderiv ℝ u) p (e 0) (e 0) +
      Γ (u p) (fderiv ℝ u p (e 0)) (fderiv ℝ u p (e 0))) +
      (fderiv ℝ (fderiv ℝ u) p (e 1) (e 1) +
      Γ (u p) (fderiv ℝ u p (e 1)) (fderiv ℝ u p (e 1))) = 0 := by
    change (∑ i : Fin 2, ConnectionVariation.covDerivAlong Γ u
      (fun x => fderiv ℝ u x (e i)) (e i) p) = 0 at hharm
    simp only [ConnectionVariation.covDerivAlong, fderiv_column hu, Fin.sum_univ_two] at hharm
    exact hharm
  have ht' := congrArg (fderiv ℝ r (u p)) ht
  simp only [map_add, map_zero] at ht'
  rw [← heq.fderiv.fderiv_eq, Fin.sum_univ_two, Fin.sum_univ_two,
    second_fderiv_comp hr hu, second_fderiv_comp hr hu, ← hdu]
  erw [hH 0, hH 1]
  linarith only [ht']

theorem suHarmonic_observation_laplacian_bound [CompactSpace M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {s : M → ℝ} (hs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ s) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (φ : LoopPlane → M), ContMDiff (𝓡 2) (𝓡 n) ∞ φ →
      ∀ p : LoopPlane,
      (let u := extChartAt (𝓡 n) (φ p) ∘ φ
       let Γ := CoordinateExponential.christoffelBilinear
         (g.pullbackCoefficients (extChartAt (𝓡 n) (φ p)).symm)
       ∑ i : Fin 2, ConnectionVariation.covDerivAlong Γ u
         (fun x => fderiv ℝ u x (EuclideanSpace.basisFun (Fin 2) ℝ i))
           (EuclideanSpace.basisFun (Fin 2) ℝ i) p = 0) →
      |∑ i : Fin 2, fderiv ℝ (fderiv ℝ (s ∘ φ)) p (EuclideanSpace.basisFun (Fin 2) ℝ i)
        (EuclideanSpace.basisFun (Fin 2) ℝ i)| ≤ B * m60EnergyDensity g φ p := by
  obtain ⟨B, hB, hbound⟩ := D.exists_metric_hessian_bound_on_compact hs isCompact_univ
  refine ⟨2 * B, by positivity, fun φ hφ p hharm => ?_⟩
  rw [harmonic_composition_laplacian D hs hφ p hharm]
  calc
    _ ≤ ∑ i : Fin 2, |D.hessian s (φ p)
        (mfderiv (𝓡 2) (𝓡 n) φ p (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (mfderiv (𝓡 2) (𝓡 n) φ p (EuclideanSpace.basisFun (Fin 2) ℝ i))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 2, B * m60AreaGram g φ p i i :=
      Finset.sum_le_sum fun i _ => hbound (φ p) (mem_univ _) _
    _ = _ := by
      simp only [m60EnergyDensity, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
      ring

theorem suHarmonic_observation_vector_laplacian_bound [CompactSpace M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) {k : ℕ}
    {e : M → EuclideanSpace ℝ (Fin k)} (he : ContMDiff (𝓡 n) (𝓡 k) ∞ e) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (φ : LoopPlane → M), ContMDiff (𝓡 2) (𝓡 n) ∞ φ →
      ∀ p : LoopPlane,
      (let u := extChartAt (𝓡 n) (φ p) ∘ φ
       let Γ := CoordinateExponential.christoffelBilinear
         (g.pullbackCoefficients (extChartAt (𝓡 n) (φ p)).symm)
       ∑ i : Fin 2, ConnectionVariation.covDerivAlong Γ u
         (fun x => fderiv ℝ u x (EuclideanSpace.basisFun (Fin 2) ℝ i))
           (EuclideanSpace.basisFun (Fin 2) ℝ i) p = 0) →
      ‖∑ i : Fin 2, fderiv ℝ (fderiv ℝ (e ∘ φ)) p (EuclideanSpace.basisFun (Fin 2) ℝ i)
        (EuclideanSpace.basisFun (Fin 2) ℝ i)‖ ≤ B * m60EnergyDensity g φ p := by
  have hs (j : Fin k) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => e x j) :=
    (contMDiff_iff_contDiff.mpr (EuclideanSpace.proj j).contDiff).comp he
  choose B hB hbound using fun j : Fin k => suHarmonic_observation_laplacian_bound D (hs j)
  refine ⟨∑ j, B j, Finset.sum_nonneg (fun j _ => hB j), fun φ hφ p hharm => ?_⟩
  let U := e ∘ φ
  let W := ∑ i : Fin 2, fderiv ℝ (fderiv ℝ U) p (EuclideanSpace.basisFun (Fin 2) ℝ i)
    (EuclideanSpace.basisFun (Fin 2) ℝ i)
  let b := EuclideanSpace.basisFun (Fin k) ℝ
  have hU : ContDiff ℝ ∞ U := contMDiff_iff_contDiff.mp (he.comp hφ)
  have hc (j : Fin k) : W j =
      ∑ i : Fin 2, fderiv ℝ (fderiv ℝ ((fun x => e x j) ∘ φ)) p
        (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
    simp only [W, WithLp.ofLp_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    let L := EuclideanSpace.proj (𝕜 := ℝ) j
    change _ = fderiv ℝ (fderiv ℝ (L ∘ U)) p _ _
    rw [second_fderiv_comp (L.contDiff.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
      (hU.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))]
    have hL : fderiv ℝ L = fun _ => L := funext fun _ => L.fderiv
    rw [hL]
    erw [fderiv_const]
    change _ = 0 + _
    exact (zero_add _).symm
  calc
    ‖W‖ = ‖∑ j, b.repr W j • b j‖ := congrArg norm (b.sum_repr W).symm
    _ ≤ ∑ j, ‖b.repr W j • b j‖ := norm_sum_le _ _
    _ = ∑ j, |W j| := by simp only [norm_smul, b, EuclideanSpace.basisFun_repr,
      Real.norm_eq_abs, OrthonormalBasis.norm_eq_one, mul_one]
    _ ≤ ∑ j, B j * m60EnergyDensity g φ p := by
      apply Finset.sum_le_sum
      intro j _
      rw [hc j]
      exact hbound j φ hφ p hharm
    _ = _ := (Finset.sum_mul _ _ _).symm

private theorem radial_comparison_tail_decay {a c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    {E H H' : ℝ → ℝ} (hE : Continuous E) (hH : Continuous H) (hH' : Continuous H')
    (hEi : IntegrableOn E (Ioi a)) (hEn : ∀ t > a, 0 ≤ E t)
    (hder : ∀ t > a, HasDerivAt H (H' t) t)
    (hlower : ∀ t > a, c * E t ≤ H' t)
    (hbound : ∀ t > a, |H t| ≤ C * E t) :
    ∀ s > a, ∀ t ≥ s, (∫ x in Ioi t, E x) ≤
      (∫ x in Ioi s, E x) * Real.exp (-(c / C) * (t - s)) := by
  have hHi : IntegrableOn H (Ioi a) := (hEi.const_mul C).mono'
    hH.aestronglyMeasurable.restrict (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simpa only [Real.norm_eq_abs] using hbound t ht)
  have hmono : MonotoneOn H (Ioi a) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi a) hH.continuousOn
    · intro t ht
      exact (hder t (by simpa only [interior_Ioi, mem_Ioi] using ht)).hasDerivWithinAt
    · intro t ht
      have ht' : a < t := by simpa only [interior_Ioi, mem_Ioi] using ht
      exact (mul_nonneg hc.le (hEn t ht')).trans (hlower t ht')
  have hnonpos (s : ℝ) (hs : a < s) : H s ≤ 0 := by
    by_contra h
    have hspos : 0 < H s := lt_of_not_ge h
    have hci : IntegrableOn (fun _ : ℝ => H s) (Ioi s) :=
      (hHi.mono_set (Ioi_subset_Ioi hs.le)).mono' aestronglyMeasurable_const (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [Real.norm_eq_abs, abs_of_pos hspos]
        exact hmono hs (hs.trans ht) ht.le)
    rcases integrable_const_iff.mp hci with hz | hf
    · exact hspos.ne' hz
    · have hh := hf.measure_univ_lt_top
      simp only [Measure.restrict_apply_univ, Real.volume_Ioi, lt_self_iff_false] at hh
  let F := fun t => ∫ x in Ioi t, E x
  have htail (s : ℝ) (hs : a < s) : c * F s ≤ C * E s := by
    have hfinite (t : ℝ) (hst : s ≤ t) : c * (∫ x in s..t, E x) ≤ -H s := by
      have h := intervalIntegral.integral_mono_on hst
        ((hE.intervalIntegrable (μ := volume) s t).const_mul c)
        (hH'.intervalIntegrable (μ := volume) s t)
        (fun x hx => hlower x (hs.trans_le hx.1))
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => ?_)
          (hH'.intervalIntegrable s t)] at h
      · linarith only [h, hnonpos t (hs.trans_le hst)]
      · rw [uIcc_of_le hst] at hx
        exact hder x (hs.trans_le hx.1)
    have ht : c * F s ≤ -H s := le_of_tendsto
      ((intervalIntegral_tendsto_integral_Ioi s (hEi.mono_set (Ioi_subset_Ioi hs.le))
        tendsto_id).const_mul c)
      ((eventually_ge_atTop s).mono fun t ht => hfinite t ht)
    exact ht.trans ((neg_le_abs _).trans (hbound s hs))
  have hFeq (s : ℝ) (hs : a ≤ s) : F s = F a - ∫ x in a..s, E x := by
    have h := intervalIntegral.integral_interval_add_Ioi hEi
      (hEi.mono_set (Ioi_subset_Ioi hs))
    change (∫ x in a..s, E x) + F s = F a at h
    linarith only [h]
  have hFder (s : ℝ) (hs : a < s) : HasDerivAt F (-E s) s := by
    have hp := (intervalIntegral.integral_hasDerivAt_right (hE.intervalIntegrable a s)
      hE.aestronglyMeasurable.stronglyMeasurableAtFilter hE.continuousAt).const_sub (F a)
    apply hp.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hs] with t ht
    exact hFeq t ht.le
  intro s hs t hst
  have hf : ContinuousOn (fun x => -F x) (Icc s t) := by
    intro x hx
    exact (hFder x (hs.trans_le hx.1)).continuousAt.neg.continuousWithinAt
  have h := Poincare.ODE.mul_exp_neg_integral_le_of_deriv_add_mul_nonneg hst hf
    (q := fun _ => c / C) (f' := E) continuousOn_const intervalIntegrable_const
    (fun x hx => by
      have h := (hFder x (hs.trans hx.1)).neg
      simp only [neg_neg] at h
      exact h)
    (by
      intro x hx
      have hh := htail x (hs.trans hx.1)
      have heq : (C * E x - c * F x) / C = E x + c / C * -F x := by
        field_simp
        ring
      rw [← heq]
      exact div_nonneg (sub_nonneg.mpr hh) hC.le)
  have he : -(∫ _ in s..t, c / C) = -(c / C) * (t - s) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [he, neg_mul, neg_le_neg_iff] at h
  exact h

private def cylinderCoordinates : (ℝ × ℝ) ≃ᵐ LoopPlane :=
  MeasurableEquiv.finTwoArrow.symm.trans (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))

private theorem cylinderCoordinates_apply (x : ℝ × ℝ) :
    cylinderCoordinates x = suCylinderPoint x.1 x.2 := by
  ext i
  fin_cases i <;> simp [cylinderCoordinates, suCylinderPoint, EuclideanSpace.basisFun_apply]

private theorem cylinderCoordinates_preserving : MeasurePreserving cylinderCoordinates :=
  (volume_preserving_finTwoArrow ℝ).symm.trans
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).symm

private theorem cylinder_rectangle_integral {q : LoopPlane → ℝ} (hq : Continuous q)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    (∫ x in cylinderCoordinates '' (Icc a b ×ˢ Icc c d), q x) =
      ∫ t in a..b, ∫ θ in c..d, q (suCylinderPoint t θ) := by
  rw [cylinderCoordinates_preserving.setIntegral_image_emb
    cylinderCoordinates.measurableEmbedding q]
  have hp : Continuous (fun x : ℝ × ℝ => suCylinderPoint x.1 x.2) := by
    unfold suCylinderPoint
    fun_prop
  simp_rw [cylinderCoordinates_apply]
  erw [setIntegral_prod _ (((hq.comp hp).continuousOn).integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc))]
  simp_rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hcd]
  exact (intervalIntegral.integral_of_le hab).symm

private theorem cylinder_disk_mass {q : LoopPlane → ℝ} (hq : Continuous q)
    (hqn : ∀ x, 0 ≤ q x) {T : ℝ} (hT : 2 ≤ T)
    (hperiod : ∀ x, q (x + T • EuclideanSpace.basisFun (Fin 2) ℝ 1) = q x)
    (t θ : ℝ) :
    (∫ x in Metric.closedBall (suCylinderPoint t θ) 1, q x) ≤
      ∫ s in (t - 1)..(t + 1), ∫ r in 0..T, q (suCylinderPoint s r) := by
  let K := Icc (t - 1) (t + 1) ×ˢ Icc (θ - 1) (θ - 1 + T)
  have hp : Continuous (fun x : ℝ × ℝ => suCylinderPoint x.1 x.2) := by
    unfold suCylinderPoint
    fun_prop
  have hK : IsCompact (cylinderCoordinates '' K) := by
    have he : (cylinderCoordinates : ℝ × ℝ → LoopPlane) =
        (fun x => suCylinderPoint x.1 x.2) := funext cylinderCoordinates_apply
    rw [he]
    exact (isCompact_Icc.prod isCompact_Icc).image hp
  have hsub : Metric.closedBall (suCylinderPoint t θ) 1 ⊆ cylinderCoordinates '' K := by
    intro x hx
    have hn : ‖x - suCylinderPoint t θ‖ ≤ 1 := Metric.mem_closedBall.mp hx
    have hcoord (i : Fin 2) : |x i - suCylinderPoint t θ i| ≤ 1 := by
      exact (PiLp.norm_apply_le (x - suCylinderPoint t θ) i).trans hn
    have h0 := abs_le.mp (hcoord 0)
    have h1 := abs_le.mp (hcoord 1)
    simp only [suCylinderPoint, PiLp.add_apply, PiLp.smul_apply,
      EuclideanSpace.basisFun_apply, PiLp.single_apply, smul_eq_mul] at h0 h1
    norm_num at h0 h1
    refine ⟨(x 0, x 1), ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩, ?_⟩
    rw [cylinderCoordinates_apply]
    ext i
    fin_cases i <;> simp [suCylinderPoint, EuclideanSpace.basisFun_apply]
  calc
    _ ≤ ∫ x in cylinderCoordinates '' K, q x :=
      setIntegral_mono_set (hq.continuousOn.integrableOn_compact hK)
        (Eventually.of_forall hqn) hsub.eventuallyLE
    _ = ∫ s in (t - 1)..(t + 1), ∫ r in (θ - 1)..(θ - 1 + T),
        q (suCylinderPoint s r) :=
      cylinder_rectangle_integral hq (by linarith) (by linarith)
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro s _
      have hper : Function.Periodic (fun r => q (suCylinderPoint s r)) T := by
        intro r
        have he : suCylinderPoint s (r + T) =
            suCylinderPoint s r + T • EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
          simp only [suCylinderPoint, add_smul]
          abel
        change q (suCylinderPoint s (r + T)) = q (suCylinderPoint s r)
        rw [he, hperiod]
      simpa only [zero_add] using hper.intervalIntegral_add_eq (θ - 1) 0

private theorem energy_translate (g : RiemannianMetric n M)
    {φ : LoopPlane → M} (hφ : ContMDiff (𝓡 2) (𝓡 n) ∞ φ) (a x : LoopPlane) :
    m60EnergyDensity g (fun y => φ (a + y)) x = m60EnergyDensity g φ (a + x) := by
  have hs : HasMFDerivAt (𝓡 2) (𝓡 2) (fun y : LoopPlane => a + y) x
      (ContinuousLinearMap.id ℝ LoopPlane) :=
    ((hasFDerivAt_id x).const_add a).hasMFDerivAt
  have hd := mfderiv_comp x ((hφ (a + x)).mdifferentiableAt (by simp)) hs.mdifferentiableAt
  rw [hs.mfderiv] at hd
  unfold m60EnergyDensity m60AreaGram
  change (1 / 2 : ℝ) * Matrix.trace (fun i j => g.inner _
    (mfderiv (𝓡 2) (𝓡 n) (φ ∘ (fun y => a + y)) x _)
    (mfderiv (𝓡 2) (𝓡 n) (φ ∘ (fun y => a + y)) x _)) = _
  rw [hd]
  rfl

private theorem harmonic_unit_disk_estimate [CompactSpace M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ (φ : LoopPlane → M),
      ContMDiff (𝓡 2) (𝓡 n) ∞ φ → ∀ p : LoopPlane,
      (∀ b : M, ∀ x ∈ Metric.ball p 1, φ x ∈ (extChartAt (𝓡 n) b).source →
        let u := extChartAt (𝓡 n) b ∘ φ
        let Γ := CoordinateExponential.christoffelBilinear
          (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm)
        ∑ i : Fin 2, ConnectionVariation.covDerivAlong Γ u
          (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin 2) ℝ i))
            (EuclideanSpace.basisFun (Fin 2) ℝ i) x = 0) →
      (∫ x in Metric.closedBall p 1, m60EnergyDensity g φ x) ≤ ε →
      m60EnergyDensity g φ p ≤ C * (∫ x in Metric.closedBall p 1, m60EnergyDensity g φ x) := by
  obtain ⟨ε, C, hε, hC, hest⟩ := m60AlphaMap_small_energy D
  refine ⟨ε / 2, C, by positivity, hC, fun φ hφ p hharm hsmall => ?_⟩
  let ψ := fun x => φ (p + x)
  have hψ : ContMDiff (𝓡 2) (𝓡 n) ∞ ψ :=
    hφ.comp (contMDiff_iff_contDiff.mpr (contDiff_const.add contDiff_id))
  have hm : (∫ x in Metric.closedBall 0 1, 2 * m60EnergyDensity g ψ x / 1) =
      2 * (∫ x in Metric.closedBall p 1, m60EnergyDensity g φ x) := by
    simp only [div_one, ψ, energy_translate g hφ]
    rw [integral_const_mul, suSetIntegral_closedBall_add_left]
  have heq (b : M) (x : LoopPlane) (hx : x ∈ Metric.ball 0 1)
      (hb : ψ x ∈ (extChartAt (𝓡 n) b).source) :
      let u := extChartAt (𝓡 n) b ∘ ψ
      let Γ := CoordinateExponential.christoffelBilinear
        (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm)
      ∑ i : Fin 2, ConnectionVariation.covDerivAlong Γ u
        (fun y => (1 ^ 2 + 2 * m60EnergyDensity g ψ y / 1) ^ ((1 : ℝ) - 1) •
          fderiv ℝ u y (EuclideanSpace.basisFun (Fin 2) ℝ i))
            (EuclideanSpace.basisFun (Fin 2) ℝ i) x = 0 := by
    have hpx : p + x ∈ Metric.ball p 1 := by simpa only [Metric.mem_ball, dist_self_add_left,
      dist_zero_right] using hx
    have h := hharm b (p + x) hpx hb
    simp only [sub_self, Real.rpow_zero, one_smul]
    simp only [ConnectionVariation.covDerivAlong] at h ⊢
    let u := extChartAt (𝓡 n) b ∘ φ
    change (∑ i : Fin 2, (fderiv ℝ
      (fun y => fderiv ℝ (fun z => u (p + z)) y (EuclideanSpace.basisFun (Fin 2) ℝ i)) x
        (EuclideanSpace.basisFun (Fin 2) ℝ i) +
      CoordinateExponential.christoffelBilinear
        (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm) (u (p + x))
          (fderiv ℝ (fun z => u (p + z)) x (EuclideanSpace.basisFun (Fin 2) ℝ i))
          (fderiv ℝ (fun z => u (p + z)) x (EuclideanSpace.basisFun (Fin 2) ℝ i)))) = 0
    simp only [fderiv_comp_add_left]
    have hc (i : Fin 2) : fderiv ℝ
        (fun y => fderiv ℝ u (p + y) (EuclideanSpace.basisFun (Fin 2) ℝ i)) x =
        fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin 2) ℝ i)) (p + x) :=
      fderiv_comp_add_left (f := fun y => fderiv ℝ u y
        (EuclideanSpace.basisFun (Fin 2) ℝ i)) p
    simp only [hc]
    exact h
  have h := hest 1 1 1 (by norm_num) le_rfl (by norm_num) (by norm_num) le_rfl ψ hψ
    (fun _ => 1) contDiff_const (fun _ => zero_lt_one)
    (by
      intro x hx
      norm_num [fderiv_const]) heq (by rw [hm]; linarith only [hsmall])
  rw [hm] at h
  simp only [one_pow, one_mul, div_one, ψ, energy_translate g hφ, add_zero] at h
  linarith only [h]

theorem suHarmonicCylinder_small_tail [CompactSpace M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) {φ : LoopPlane → M}
    (hφ : ContMDiff (𝓡 2) (𝓡 n) ∞ φ) {T : ℝ} (hT : 2 ≤ T)
    (hperiod : ∀ x, φ (x + T • EuclideanSpace.basisFun (Fin 2) ℝ 1) = φ x)
    (hharm : ∀ b : M, ∀ x : LoopPlane, 0 < x 0 → φ x ∈ (extChartAt (𝓡 n) b).source →
      let u := extChartAt (𝓡 n) b ∘ φ
      let Γ := CoordinateExponential.christoffelBilinear
        (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm)
      ∑ i : Fin 2, ConnectionVariation.covDerivAlong Γ u
        (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin 2) ℝ i))
          (EuclideanSpace.basisFun (Fin 2) ℝ i) x = 0)
    (hfinite : IntegrableOn (fun t => ∫ θ in 0..T,
      m60EnergyDensity g φ (suCylinderPoint t θ)) (Ioi 0)) :
    ∃ C : ℝ, 0 < C ∧
      (∀ᶠ t in atTop, ∀ θ : ℝ, m60EnergyDensity g φ (suCylinderPoint t θ) ≤
        C * ∫ s in Ioi (t - 1), ∫ r in 0..T, m60EnergyDensity g φ (suCylinderPoint s r)) ∧
      Tendsto (fun t => ∫ θ in 0..T, m60EnergyDensity g φ (suCylinderPoint t θ)) atTop (𝓝 0) := by
  let q := m60EnergyDensity g φ
  let E := fun t => ∫ θ in 0..T, q (suCylinderPoint t θ)
  let F := fun t => ∫ s in Ioi (t - 1), E s
  have hq : Continuous q := by
    change Continuous (fun x => (1 / 2 : ℝ) * Matrix.trace (m60AreaGram g φ x))
    simp only [Matrix.trace_fin_two]
    exact continuous_const.mul ((m60AreaGram_entry_contDiff g hφ 0 0).continuous.add
      (m60AreaGram_entry_contDiff g hφ 1 1).continuous)
  have hqn := m60EnergyDensity_nonneg g φ
  have hperq (x : LoopPlane) : q (x + T • EuclideanSpace.basisFun (Fin 2) ℝ 1) = q x := by
    have he : (fun y => φ (T • EuclideanSpace.basisFun (Fin 2) ℝ 1 + y)) = φ := by
      funext y
      rw [add_comm, hperiod]
    have h := energy_translate g hφ (T • EuclideanSpace.basisFun (Fin 2) ℝ 1) x
    rw [he] at h
    simpa only [add_comm] using h.symm
  have hEn (t : ℝ) : 0 ≤ E t :=
    intervalIntegral.integral_nonneg (by linarith) (fun θ _ => hqn _)
  have hF : Tendsto F atTop (𝓝 0) := by
    apply tendsto_integral_Ioi_zero
    exact tendsto_atTop_atTop.mpr fun b => ⟨b + 1, fun t ht => by linarith⟩
  have hmass (t θ : ℝ) (ht : 1 < t) : (∫ x in Metric.closedBall (suCylinderPoint t θ) 1, q x)
      ≤ F t := by
    apply (cylinder_disk_mass hq hqn hT hperq t θ).trans
    rw [intervalIntegral.integral_of_le (by linarith : t - 1 ≤ t + 1)]
    apply setIntegral_mono_set (hfinite.mono_set (Ioi_subset_Ioi (by linarith)))
      (Eventually.of_forall hEn) Ioc_subset_Ioi_self.eventuallyLE
  obtain ⟨ε, C, hε, hC, hest⟩ := harmonic_unit_disk_estimate D
  have hsmall : ∀ᶠ t in atTop, F t ≤ ε :=
    (hF.eventually (gt_mem_nhds hε)).mono fun _ h => h.le
  have hpoint : ∀ᶠ t in atTop, ∀ θ : ℝ, q (suCylinderPoint t θ) ≤ C * F t := by
    filter_upwards [hsmall, eventually_gt_atTop (1 : ℝ)] with t ht ht1
    intro θ
    apply (hest φ hφ (suCylinderPoint t θ) (fun b x hx hb => hharm b x ?_ hb)
      ((hmass t θ ht1).trans ht)).trans
    · exact mul_le_mul_of_nonneg_left (hmass t θ ht1) hC.le
    · have hn : ‖x - suCylinderPoint t θ‖ < 1 := Metric.mem_ball.mp hx
      have hc := (PiLp.norm_apply_le (x - suCylinderPoint t θ) 0).trans_lt hn
      change |x 0 - suCylinderPoint t θ 0| < 1 at hc
      rw [cylinderPoint_zero, abs_lt] at hc
      linarith only [hc.1, ht1]
  have hupper : ∀ᶠ t in atTop, E t ≤ T * C * F t := hpoint.mono fun t ht => by
    have hi := (hq.comp (show Continuous (suCylinderPoint t) by
      unfold suCylinderPoint; fun_prop)).intervalIntegrable (μ := volume) 0 T
    have h := intervalIntegral.integral_mono (by linarith : 0 ≤ T) hi intervalIntegrable_const ht
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
    exact h.trans_eq (by ring)
  have ht := hF.const_mul (T * C)
  rw [mul_zero] at ht
  exact ⟨C, hC, hpoint, squeeze_zero' (Eventually.of_forall hEn) hupper ht⟩

theorem suHarmonicCylinder_energy_decay [CompactSpace M] [T2Space M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) {k : ℕ}
    {e : M → EuclideanSpace ℝ (Fin k)} (he : ContMDiff (𝓡 n) (𝓡 k) ∞ e)
    (hi : ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 k) e x))
    {φ : LoopPlane → M} (hφ : ContMDiff (𝓡 2) (𝓡 n) ∞ φ) {T : ℝ} (hT : 2 ≤ T)
    (hperiod : ∀ x, φ (x + T • EuclideanSpace.basisFun (Fin 2) ℝ 1) = φ x)
    (hharm : ∀ b : M, ∀ x : LoopPlane, 0 < x 0 → φ x ∈ (extChartAt (𝓡 n) b).source →
      let u := extChartAt (𝓡 n) b ∘ φ
      let Γ := CoordinateExponential.christoffelBilinear
        (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm)
      ∑ i : Fin 2, ConnectionVariation.covDerivAlong Γ u
        (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin 2) ℝ i))
          (EuclideanSpace.basisFun (Fin 2) ℝ i) x = 0)
    (hfinite : IntegrableOn (fun t => ∫ θ in 0..T,
      m60EnergyDensity g φ (suCylinderPoint t θ)) (Ioi 0)) :
    ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ ∀ s > a, ∀ t ≥ s,
      (∫ r in Ioi t, ∫ θ in 0..T, m60EnergyDensity g φ (suCylinderPoint r θ)) ≤
      (∫ r in Ioi s, ∫ θ in 0..T, m60EnergyDensity g φ (suCylinderPoint r θ)) *
        Real.exp (-κ * (t - s)) := by
  obtain ⟨c, hc, hlower⟩ := suEmbedding_differential_lower_bound g e he hi
  obtain ⟨B, hB, hlap⟩ := suHarmonic_observation_vector_laplacian_bound D he
  obtain ⟨A, hA, hupper⟩ := exists_observed_derivative_energy_bound g e (he.of_le (by simp))
  let U := e ∘ φ
  let Y := cylinderColumn U 0
  let Z := cylinderColumn U 1
  let w := cylinderCentered U T
  let v := cylinderCentered Y T
  let L := fun x => cylinderColumn Y 0 x + cylinderColumn Z 1 x
  let Q := m60EnergyDensity g φ
  let E := fun t => ∫ θ in 0..T, Q (suCylinderPoint t θ)
  let H := fun t => ∫ θ in 0..T, inner ℝ (w (suCylinderPoint t θ)) (Y (suCylinderPoint t θ))
  let S := fun x => ‖v x‖ ^ 2 + ‖Z x‖ ^ 2 + inner ℝ (w x) (L x)
  let H' := fun t => ∫ θ in 0..T, S (suCylinderPoint t θ)
  have hTp : 0 < T := by linarith
  have hU : ContDiff ℝ ∞ U := contMDiff_iff_contDiff.mp (he.comp hφ)
  have hY := cylinderColumn_contDiff hU 0
  have hZ := cylinderColumn_contDiff hU 1
  have hw := cylinderCentered_contDiff hU T
  have hv := cylinderCentered_contDiff hY T
  have hL := (cylinderColumn_contDiff hY 0).add (cylinderColumn_contDiff hZ 1)
  have hv2 : ContDiff ℝ ∞ (fun x => ‖v x‖ ^ 2) := hv.norm_sq ℝ
  have hZ2 : ContDiff ℝ ∞ (fun x => ‖Z x‖ ^ 2) := hZ.norm_sq ℝ
  have hS : ContDiff ℝ ∞ S := (hv2.add hZ2).add (hw.inner ℝ hL)
  have hQ : ContDiff ℝ ∞ Q := by
    change ContDiff ℝ ∞ (fun x => (1 / 2 : ℝ) * Matrix.trace (m60AreaGram g φ x))
    simp only [Matrix.trace_fin_two]
    exact contDiff_const.mul ((m60AreaGram_entry_contDiff g hφ 0 0).add
      (m60AreaGram_entry_contDiff g hφ 1 1))
  have hEn (t : ℝ) : 0 ≤ E t :=
    intervalIntegral.integral_nonneg hTp.le (fun θ _ => m60EnergyDensity_nonneg g φ _)
  have hE : Continuous E := continuous_iff_continuousAt.mpr fun t =>
    (cylinderIntegral_hasDerivAt hQ T t).continuousAt
  have hH : Continuous H := continuous_iff_continuousAt.mpr fun t =>
    (cylinderIntegral_hasDerivAt (hw.inner ℝ hY) T t).continuousAt
  have hH' : Continuous H' := continuous_iff_continuousAt.mpr fun t =>
    (cylinderIntegral_hasDerivAt hS T t).continuousAt
  have hdu (x : LoopPlane) (i : Fin 2) : cylinderColumn U i x =
      mfderiv (𝓡 n) (𝓡 k) e (φ x)
        (mfderiv (𝓡 2) (𝓡 n) φ x (EuclideanSpace.basisFun (Fin 2) ℝ i)) := by
    unfold cylinderColumn U
    rw [← mfderiv_eq_fderiv, mfderiv_comp x ((he _).mdifferentiableAt (by simp))
      ((hφ _).mdifferentiableAt (by simp))]
    rfl
  have hcol (x : LoopPlane) (i : Fin 2) : ‖cylinderColumn U i x‖ ^ 2 ≤ (A + 1) * Q x := by
    apply (hupper φ (hφ.of_le (by simp)) x i).trans
    exact mul_le_mul_of_nonneg_right (by linarith) (m60EnergyDensity_nonneg g φ x)
  have hZlower (x : LoopPlane) : c * m60AreaGram g φ x 1 1 ≤ ‖Z x‖ ^ 2 := by
    change c * m60AreaGram g φ x 1 1 ≤ ‖cylinderColumn U 1 x‖ ^ 2
    rw [hdu]
    exact hlower _ _
  have hbal (t : ℝ) (ht : 0 < t) :
      (∫ θ in 0..T, m60AreaGram g φ (suCylinderPoint t θ) 1 1) = E t := by
    have h := m60HarmonicCylinder_radial_angular g hφ hTp hperiod
      (fun r hr θ => hharm (φ (suCylinderPoint r θ)) _
        (by simpa only [cylinderPoint_zero] using hr) (mem_extChartAt_source _))
      (by
        simp only [intervalIntegral.integral_const_mul]
        exact hfinite.const_mul 2) t ht
    have h0 := ((m60AreaGram_entry_contDiff g hφ 0 0).continuous.comp
      (show Continuous (suCylinderPoint t) by unfold suCylinderPoint; fun_prop)).intervalIntegrable
        (μ := volume) 0 T
    have h1 := ((m60AreaGram_entry_contDiff g hφ 1 1).continuous.comp
      (show Continuous (suCylinderPoint t) by unfold suCylinderPoint; fun_prop)).intervalIntegrable
        (μ := volume) 0 T
    change _ = ∫ θ in 0..T, (1 / 2 : ℝ) * Matrix.trace (m60AreaGram g φ (suCylinderPoint t θ))
    simp only [Matrix.trace_fin_two]
    rw [intervalIntegral.integral_const_mul]
    erw [intervalIntegral.integral_add h0 h1, h]
    simp only [Function.comp_def]
    ring
  let η := c / (2 * (B + 1))
  have hη : 0 < η := by dsimp only [η]; positivity
  have hsmall0 : 0 < η ^ 2 / (4 * T * (A + 1)) := by positivity
  obtain ⟨_, _, _, hEt⟩ := suHarmonicCylinder_small_tail D hφ hT hperiod hharm hfinite
  obtain ⟨a₀, ha₀⟩ := eventually_atTop.mp (hEt.eventually (gt_mem_nhds hsmall0))
  let a := max a₀ 1
  have hap : 0 < a := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hosc (t : ℝ) (ht : a < t) (θ : ℝ) (hθ : θ ∈ Icc 0 T) :
      ‖w (suCylinderPoint t θ)‖ ≤ η := by
    have hp : ContDiff ℝ ∞ (suCylinderPoint t) := by unfold suCylinderPoint; fun_prop
    have hh := circleMean_poincare (hU.comp hp) hTp hθ
    have hd (r : ℝ) : deriv (U ∘ suCylinderPoint t) r = Z (suCylinderPoint t r) :=
      ((hU.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt r
        (cylinderPoint_second t r)).deriv
    simp_rw [hd] at hh
    have hh' : ‖w (suCylinderPoint t θ)‖ ^ 2 ≤
        4 * T * (∫ r in 0..T, ‖Z (suCylinderPoint t r)‖ ^ 2) := by
      simpa only [w, cylinderCentered, cylinderMean, cylinderPoint_zero,
        Function.comp_def] using hh
    have hb := intervalIntegral.integral_mono hTp.le
      ((hZ.continuous.norm.pow 2).comp hp.continuous |>.intervalIntegrable (μ := volume) 0 T)
      ((hQ.continuous.comp hp.continuous).intervalIntegrable 0 T |>.const_mul (A + 1))
      (fun r => hcol _ 1)
    rw [intervalIntegral.integral_const_mul] at hb
    change (∫ r in 0..T, ‖Z (suCylinderPoint t r)‖ ^ 2) ≤ (A + 1) * E t at hb
    have hs := (lt_div_iff₀ (by positivity : 0 < 4 * T * (A + 1))).mp
      (ha₀ t ((le_max_left _ _).trans ht.le))
    change E t * (4 * T * (A + 1)) < η ^ 2 at hs
    apply le_of_sq_le_sq _ hη.le
    nlinarith only [hh', mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 4 * T), hs.le]
  have hder (t : ℝ) : HasDerivAt H (H' t) t :=
    cylinderRadialComparison_hasDerivAt hU hTp t (fun x => congrArg e (hperiod x))
  have hderlower (t : ℝ) (ht : a < t) : c / 2 * E t ≤ H' t := by
    have hp : Continuous (suCylinderPoint t) := by unfold suCylinderPoint; fun_prop
    have hreact (θ : ℝ) (hθ : θ ∈ Icc 0 T) :
        -(c / 2) * Q (suCylinderPoint t θ) ≤
          inner ℝ (w (suCylinderPoint t θ)) (L (suCylinderPoint t θ)) := by
      have hl := hlap φ hφ (suCylinderPoint t θ)
        (hharm (φ (suCylinderPoint t θ)) _
          (by rw [cylinderPoint_zero]; exact hap.trans ht) (mem_extChartAt_source _))
      have he : L (suCylinderPoint t θ) = ∑ i : Fin 2,
          fderiv ℝ (fderiv ℝ U) (suCylinderPoint t θ) (EuclideanSpace.basisFun (Fin 2) ℝ i)
            (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
        simp only [L, Y, Z, cylinderColumn]
        unfold cylinderColumn
        rw [fderiv_column (hU.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)),
          fderiv_column (hU.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)), Fin.sum_univ_two]
      rw [← he] at hl
      have hh := (abs_real_inner_le_norm (w (suCylinderPoint t θ))
        (L (suCylinderPoint t θ))).trans (mul_le_mul (hosc t ht θ hθ) hl
          (norm_nonneg _) hη.le)
      have hb : η * B ≤ c / 2 := by dsimp only [η]; field_simp; nlinarith only [hc, hB]
      have hq := m60EnergyDensity_nonneg g φ (suCylinderPoint t θ)
      nlinarith only [(abs_le.mp hh).1, mul_le_mul_of_nonneg_right hb hq]
    have hgi := ((m60AreaGram_entry_contDiff g hφ 1 1).continuous.comp hp).intervalIntegrable
      (μ := volume) 0 T
    have hqi := (hQ.continuous.comp hp).intervalIntegrable (μ := volume) 0 T
    have hcmp := intervalIntegral.integral_mono_on hTp.le
      ((hgi.const_mul c).sub (hqi.const_mul (c / 2)))
      ((hS.continuous.comp hp).intervalIntegrable 0 T)
      (fun θ hθ => by
        dsimp only [S, Function.comp_def]
        have h1 := hZlower (suCylinderPoint t θ)
        have h2 := hreact θ hθ
        have h3 := sq_nonneg ‖v (suCylinderPoint t θ)‖
        nlinarith only [h1, h2, h3])
    simp only [Function.comp_def] at hcmp
    erw [intervalIntegral.integral_sub (hgi.const_mul c) (hqi.const_mul (c / 2)),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, hbal t (hap.trans ht)] at hcmp
    change c * E t - c / 2 * E t ≤ H' t at hcmp
    linarith only [hcmp]
  have hHbound (t : ℝ) : |H t| ≤ (2 * T * (A + 1)) * E t := by
    apply (cylinderRadialComparison_bound hU hTp t).trans
    have hp : Continuous (suCylinderPoint t) := by unfold suCylinderPoint; fun_prop
    have hb := intervalIntegral.integral_mono hTp.le
      (((hY.continuous.norm.pow 2).add (hZ.continuous.norm.pow 2)).comp hp
        |>.intervalIntegrable (μ := volume) 0 T)
      ((hQ.continuous.comp hp).intervalIntegrable 0 T |>.const_mul (2 * (A + 1)))
      (fun θ => by
        dsimp only [Function.comp_def, Pi.add_apply, Pi.pow_apply]
        nlinarith only [hcol (suCylinderPoint t θ) 0, hcol (suCylinderPoint t θ) 1])
    rw [intervalIntegral.integral_const_mul] at hb
    exact (mul_le_mul_of_nonneg_left hb hTp.le).trans_eq (by
      dsimp only [E, Function.comp_def]
      ring)
  refine ⟨a, (c / 2) / (2 * T * (A + 1)), hap, by positivity, ?_⟩
  exact radial_comparison_tail_decay (by positivity) (by positivity) hE hH hH'
    (hfinite.mono_set (Ioi_subset_Ioi hap.le)) (fun t _ => hEn t) (fun t _ => hder t)
    hderlower (fun t _ => hHbound t)

end PoincareConjecture.M60
