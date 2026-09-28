import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityPolarL2
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerSlicing
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularitySliceMean
import PoincareConjecture.Proofs.M03.Existence.DeTurckDomainRegularityNative












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology SchwartzMap LineDeriv InnerProductSpace ContDiff ENNReal

namespace PoincareConjecture.M65Interior

open EuclideanTranslationNative EuclideanMollificationNative DeTurckDomainRegularityNative

private theorem angularPoint_basis (t : ℝ) :
    Proofs.M58.angularPoint t =
      Real.cos t • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
        Real.sin t • EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
  ext i
  fin_cases i <;> simp [Proofs.M58.angularPoint, EuclideanSpace.basisFun_apply]

private theorem polarPlane_angular_hasDerivAt (x : LoopPlane) (r t : ℝ) :
    HasDerivAt (fun s => polarPlane x (r, s))
      ((-r * Real.sin t) • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
        (r * Real.cos t) • EuclideanSpace.basisFun (Fin 2) ℝ 1) t := by
  have h := (((Real.hasDerivAt_cos t).const_mul r).smul_const
    (EuclideanSpace.basisFun (Fin 2) ℝ 0)).add
      (((Real.hasDerivAt_sin t).const_mul r).smul_const
        (EuclideanSpace.basisFun (Fin 2) ℝ 1))
  have heq : (fun s => polarPlane x (r, s)) =
      (fun s => x + (r * Real.cos s) • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
        (r * Real.sin s) • EuclideanSpace.basisFun (Fin 2) ℝ 1) := by
    funext s
    simp only [polarPlane, angularPoint_basis, smul_add, smul_smul, add_assoc]
  rw [heq]
  simpa only [mul_neg, neg_mul, add_assoc, Pi.add_apply] using h.const_add x







theorem weakPair_polar_AC (u : Lp ℝ 2 (volume : Measure LoopPlane))
    (d : Fin 2 → Lp ℝ 2 (volume : Measure LoopPlane))
    (hweak : ∀ i (φ : 𝓢(LoopPlane, ℝ)),
      ⟪d i, φ.toLp 2 volume⟫_ℝ =
        -(∫ z, u z * fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i)))
    (x : LoopPlane) {ε : ℝ} (R : ℝ) (hε : 0 < ε) :
    ∀ᵐ r ∂(volume.restrict (Icc ε R)),
      MemLp (fun t => -r * Real.sin t * d 0 (polarPlane x (r, t)) +
        r * Real.cos t * d 1 (polarPlane x (r, t))) 2
          (volume.restrict (Icc (-Real.pi) Real.pi)) ∧
      ∃ v : ℝ → ℝ, AbsolutelyContinuousOnInterval v (-Real.pi) Real.pi ∧
        (v =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)]
          fun t => u (polarPlane x (r, t))) ∧
        v (-Real.pi) = v Real.pi ∧
        ∀ s ∈ Icc (-Real.pi) Real.pi, ∀ t ∈ Icc (-Real.pi) Real.pi,
          v t - v s = ∫ θ in s..t,
            -r * Real.sin θ * d 0 (polarPlane x (r, θ)) +
              r * Real.cos θ * d 1 (polarPlane x (r, θ)) := by
  let mu := volume.restrict (Icc ε R)
  let nu := mu.prod (volume.restrict (Icc (-Real.pi) Real.pi))
  let T := polarPullbackL2 (E := ℝ) x R hε
  let D := polarAngularL2 x R hε
  have hT (w : Lp ℝ 2 (volume : Measure LoopPlane)) :
      T w =ᵐ[nu] fun p => w (polarPlane x p) := polarPullbackL2_ae x R hε w
  have hD (w : Fin 2 → Lp ℝ 2 (volume : Measure LoopPlane)) :
      D w =ᵐ[nu] fun p => -p.1 * Real.sin p.2 * w 0 (polarPlane x p) +
        p.1 * Real.cos p.2 * w 1 (polarPlane x p) := polarAngularL2_ae x R hε w
  have hcomp {f g : LoopPlane → ℝ} (hfg : f =ᵐ[volume] g) :
      (fun p => f (polarPlane x p)) =ᵐ[nu] fun p => g (polarPlane x p) :=
    ae_of_ae_map (polarPlane_measurePreserving x).measurable.aemeasurable
      (ae_mono (polarPlane_map_strip_le x hε)
        (Measure.ae_smul_measure hfg (ENNReal.ofReal ε)⁻¹))
  let eta (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have heta (n : ℕ) : 0 < eta n := by dsimp only [eta]; positivity
  have heta0 : Tendsto eta atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let f (n : ℕ) (r t : ℝ) := mollify (heta n) u (polarPlane x (r, t))
  have hf (n : ℕ) (r : ℝ) : ContDiff ℝ 1 (f n r) := by
    have hcircle : ContDiff ℝ ∞ (fun t => polarPlane x (r, t)) := by
      change ContDiff ℝ ∞ (fun t => x + r • Proofs.M58.angularPoint t)
      exact contDiff_const.add (Proofs.M58.contDiff_angularPoint.const_smul r)
    exact ((contDiff_mollify (heta n) u).comp hcircle).of_le (by simp)
  have hfd (n : ℕ) (r t : ℝ) : deriv (f n r) t =
      -r * Real.sin t * mollify (heta n) (d 0) (polarPlane x (r, t)) +
        r * Real.cos t * mollify (heta n) (d 1) (polarPlane x (r, t)) := by
    have h := ((contDiff_mollify (heta n) u).differentiable (by simp)
      (polarPlane x (r, t))).hasFDerivAt.comp_hasDerivAt t
        (polarPlane_angular_hasDerivAt x r t)
    change HasDerivAt (f n r) _ t at h
    rw [h.deriv, map_add, map_smul, map_smul,
      fderiv_mollify_of_weak_pairing (heta n) u (d 0) _ (hweak 0),
      fderiv_mollify_of_weak_pairing (heta n) u (d 1) _ (hweak 1)]
    rfl
  have hfu (n : ℕ) : T (mollifyL2 (heta n) u) =ᵐ[nu] fun p => f n p.1 p.2 :=
    (hT _).trans (hcomp (mollifyL2_ae_eq (heta n) u))
  have hfd' (n : ℕ) : D (fun i => mollifyL2 (heta n) (d i)) =ᵐ[nu]
      fun p => deriv (f n p.1) p.2 := by
    filter_upwards [hD (fun i => mollifyL2 (heta n) (d i)),
      hcomp (mollifyL2_ae_eq (heta n) (d 0)),
      hcomp (mollifyL2_ae_eq (heta n) (d 1))] with p hp hd0 hd1
    rw [hp, hd0, hd1, hfd]
  have hUconv := (T.continuous.tendsto u).comp (tendsto_mollifyL2 eta heta heta0 u)
  have hDconv := (D.continuous.tendsto d).comp
    (tendsto_pi_nhds.mpr (fun i => tendsto_mollifyL2 eta heta heta0 (d i)))
  have hπ : -Real.pi < Real.pi := by linarith [Real.pi_pos]
  have hperiod (n : ℕ) (r : ℝ) : f n r (-Real.pi) = f n r Real.pi := by
    dsimp only [f]
    simp only [polarPlane, Proofs.M58.angularPoint, Real.cos_neg, Real.sin_neg,
      Real.cos_pi, Real.sin_pi, neg_zero]
  have hzero (n : ℕ) : ∀ᵐ r ∂mu,
      (∫ t in -Real.pi..Real.pi, D (fun i => mollifyL2 (heta n) (d i)) (r, t)) = 0 := by
    filter_upwards [Measure.ae_ae_of_ae_prod (hfd' n)] with r hr
    have heq : (∫ t in -Real.pi..Real.pi, D (fun i => mollifyL2 (heta n) (d i)) (r, t)) =
        ∫ t in -Real.pi..Real.pi, deriv (f n r) t := by
      apply intervalIntegral.integral_congr_ae_restrict
      exact ae_restrict_of_ae_restrict_of_subset
        (by simpa only [uIoc_of_le hπ.le] using Ioc_subset_Icc_self) hr
    rw [heq, intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => ((hf n r).differentiable one_ne_zero t).hasDerivAt)
      (((hf n r).continuous_deriv (by norm_num)).intervalIntegrable (-Real.pi) Real.pi),
      ← hperiod, sub_self]
  have hmean := sliceMean_zero_of_tendsto hπ.le hDconv hzero
  have hAC := m65Product_AC_of_smooth_L2_graph hπ f hf
    (fun n => T (mollifyL2 (heta n) u))
    (fun n => D (fun i => mollifyL2 (heta n) (d i)))
    (T u) (D d) hfu hfd' hUconv hDconv
  have hmem : ∀ᵐ r ∂mu, MemLp (fun t => D d (r, t)) 2
      (volume.restrict (Icc (-Real.pi) Real.pi)) := by
    filter_upwards [(Lp.memLp (D d)).integrable_sq.prod_right_ae] with r hr
    have hm : StronglyMeasurable (fun t => D d (r, t)) :=
      (Lp.stronglyMeasurable (D d)).comp_measurable measurable_prodMk_left
    exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hr
  filter_upwards [hAC, hmem, Measure.ae_ae_of_ae_prod (hT u),
    Measure.ae_ae_of_ae_prod (hD d), hmean] with r hr hmr hur hdr hmeanr
  obtain ⟨v, hv, hvu, hvd⟩ := hr
  refine ⟨hmr.ae_eq hdr, v, hv, hvu.trans hur, ?_, ?_⟩
  · have heq := hvd (-Real.pi) ⟨le_rfl, hπ.le⟩ Real.pi ⟨hπ.le, le_rfl⟩
    rw [hmeanr] at heq
    exact (sub_eq_zero.mp heq).symm
  intro s hs t ht
  rw [hvd s hs t ht]
  apply intervalIntegral.integral_congr_ae_restrict
  exact ae_restrict_of_ae_restrict_of_subset
    ((uIoc_subset_uIcc).trans (uIcc_subset_Icc hs ht)) hdr

end PoincareConjecture.M65Interior
