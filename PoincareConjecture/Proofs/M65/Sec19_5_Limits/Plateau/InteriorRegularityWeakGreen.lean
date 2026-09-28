import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityDiskGreen
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityPolarACL












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory Filter
open scoped Topology SchwartzMap LineDeriv InnerProductSpace ContDiff ENNReal

namespace PoincareConjecture.M65Interior

open EuclideanTranslationNative EuclideanMollificationNative DeTurckDomainRegularityNative

private theorem integral_mul_tendsto {X : Type*} [MeasurableSpace X] {mu : Measure X}
    {u : ℕ → Lp ℝ 2 mu} {u0 : Lp ℝ 2 mu} (hu : Tendsto u atTop (𝓝 u0))
    {v : X → ℝ} (hv : MemLp v 2 mu) :
    Tendsto (fun n => ∫ z, u n z * v z ∂mu) atTop (𝓝 (∫ z, u0 z * v z ∂mu)) := by
  have heq (w : Lp ℝ 2 mu) : ⟪w, hv.toLp v⟫_ℝ = ∫ z, w z * v z ∂mu := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv.coeFn_toLp] with z hz
    simp only [hz, Real.inner_apply]
  simpa only [heq] using hu.inner (𝕜 := ℝ) (tendsto_const_nhds (x := hv.toLp v))

private theorem setIntegral_mul_tendsto {X : Type*} [MeasurableSpace X] {mu : Measure X}
    {u : ℕ → Lp ℝ 2 mu} {u0 : Lp ℝ 2 mu} (hu : Tendsto u atTop (𝓝 u0))
    {v : X → ℝ} (hv : MemLp v 2 mu) (S : Set X) :
    Tendsto (fun n => ∫ z in S, u n z * v z ∂mu) atTop
      (𝓝 (∫ z in S, u0 z * v z ∂mu)) := by
  let A := LpToLpRestrictCLM X ℝ ℝ mu 2 S
  have heq (w : Lp ℝ 2 mu) :
      (∫ z in S, A w z * v z ∂mu) = ∫ z in S, w z * v z ∂mu := by
    apply integral_congr_ae
    filter_upwards [LpToLpRestrictCLM_coeFn ℝ S w] with z hz
    rw [hz]
  simpa only [Function.comp_apply, heq] using
    integral_mul_tendsto ((A.continuous.tendsto u0).comp hu) (hv.restrict S)






theorem weakPair_disk_green (u : Lp ℝ 2 (volume : Measure LoopPlane))
    (d : Fin 2 → Lp ℝ 2 (volume : Measure LoopPlane))
    (hweak : ∀ i (φ : 𝓢(LoopPlane, ℝ)),
      ⟪d i, φ.toLp 2 volume⟫_ℝ =
        -(∫ z, u z * fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i)))
    (x : LoopPlane) {ε : ℝ} (R : ℝ) (hε : 0 < ε) :
    ∀ᵐ r ∂volume.restrict (Icc ε R),
      MemLp (fun θ => u (polarPlane x (r, θ))) 2
        (volume.restrict (Icc (-Real.pi) Real.pi)) ∧
      ∀ (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2),
        (∫ z in closedBall x r, d i z * test z +
          u z * fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
          r * ∫ θ in (-Real.pi)..Real.pi,
            u (polarPlane x (r, θ)) * test (polarPlane x (r, θ)) *
              Proofs.M58.angularPoint θ i := by
  let mu := volume.restrict (Icc ε R)
  let nu := volume.restrict (Icc (-Real.pi) Real.pi)
  let T := polarPullbackL2 (E := ℝ) x R hε
  have hT (w : Lp ℝ 2 (volume : Measure LoopPlane)) :
      T w =ᵐ[mu.prod nu] fun p => w (polarPlane x p) := polarPullbackL2_ae x R hε w
  have hcomp {f g : LoopPlane → ℝ} (hfg : f =ᵐ[volume] g) :
      (fun p => f (polarPlane x p)) =ᵐ[mu.prod nu] fun p => g (polarPlane x p) :=
    ae_of_ae_map (polarPlane_measurePreserving x).measurable.aemeasurable
      (ae_mono (polarPlane_map_strip_le x hε)
        (Measure.ae_smul_measure hfg (ENNReal.ofReal ε)⁻¹))
  let eta (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have heta (n : ℕ) : 0 < eta n := by dsimp only [eta]; positivity
  have heta0 : Tendsto eta atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let f (n : ℕ) := mollify (heta n) u
  have hconv (w : Lp ℝ 2 (volume : Measure LoopPlane)) :=
    tendsto_mollifyL2 eta heta heta0 w
  have hfu (n : ℕ) : T (mollifyL2 (heta n) u) =ᵐ[mu.prod nu]
      fun p => f n (polarPlane x p) :=
    (hT _).trans (hcomp (mollifyL2_ae_eq (heta n) u))
  obtain ⟨σ, hσ, hslice⟩ := m65L2_exists_slice_subsequence
    ((T.continuous.tendsto u).comp (hconv u))
  have hactual : ∀ᵐ r ∂mu, ∀ n,
      (fun θ => T (mollifyL2 (heta n) u) (r, θ)) =ᵐ[nu]
        fun θ => f n (polarPlane x (r, θ)) :=
    ae_all_iff.mpr (fun n => Measure.ae_ae_of_ae_prod (hfu n))
  filter_upwards [hslice, hactual, Measure.ae_ae_of_ae_prod (hT u),
    ae_restrict_mem measurableSet_Icc] with r hr ha hu0 hrange
  obtain ⟨hbn, hb0, hbconv⟩ := hr
  have hbu : MemLp (fun θ => u (polarPlane x (r, θ))) 2 nu := hb0.ae_eq hu0
  refine ⟨hbu, ?_⟩
  intro test i
  let b := EuclideanSpace.basisFun (Fin 2) ℝ i
  let k (θ : ℝ) := test (polarPlane x (r, θ)) * Proofs.M58.angularPoint θ i
  have hk : Continuous k :=
    (test.continuous.comp (continuous_const.add
      (Proofs.M58.contDiff_angularPoint.continuous.const_smul r))).mul
      (contDiff_euclidean.mp Proofs.M58.contDiff_angularPoint i).continuous
  have hkL2 : MemLp k 2 nu :=
    (memLp_two_iff_integrable_sq hk.aestronglyMeasurable).mpr
      ((hk.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
  let Bn (n : ℕ) := (hbn n).toLp
    (fun θ => T (mollifyL2 (heta (σ n)) u) (r, θ))
  let B0 := hb0.toLp (fun θ => T u (r, θ))
  have hBna (n : ℕ) : Bn n =ᵐ[nu] fun θ => f (σ n) (polarPlane x (r, θ)) :=
    (hbn n).coeFn_toLp.trans (ha (σ n))
  have hB0a : B0 =ᵐ[nu] fun θ => u (polarPlane x (r, θ)) :=
    hb0.coeFn_toLp.trans hu0
  have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hinterval (w : Lp ℝ 2 nu) (v : ℝ → ℝ) (hv : w =ᵐ[nu] v) :
      (∫ θ, w θ * k θ ∂nu) = ∫ θ in (-Real.pi)..Real.pi,
        v θ * test (polarPlane x (r, θ)) * Proofs.M58.angularPoint θ i := by
    rw [intervalIntegral.integral_of_le hπ,
      setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))]
    apply integral_congr_ae
    filter_upwards [hv] with θ hθ
    rw [hθ]
    exact (mul_assoc _ _ _).symm
  have hboundary : Tendsto (fun n => r * ∫ θ in (-Real.pi)..Real.pi,
      f (σ n) (polarPlane x (r, θ)) * test (polarPlane x (r, θ)) *
        Proofs.M58.angularPoint θ i) atTop
      (𝓝 (r * ∫ θ in (-Real.pi)..Real.pi,
        u (polarPlane x (r, θ)) * test (polarPlane x (r, θ)) *
          Proofs.M58.angularPoint θ i)) := by
    have h := (integral_mul_tendsto hbconv hkL2).const_mul r
    change Tendsto (fun n => r * ∫ θ, Bn n θ * k θ ∂nu) atTop
      (𝓝 (r * ∫ θ, B0 θ * k θ ∂nu)) at h
    simpa only [hinterval _ _ (hBna _), hinterval _ _ hB0a] using h
  have hpair (w : Lp ℝ 2 (volume : Measure LoopPlane)) (φ : 𝓢(LoopPlane, ℝ)) :
      Tendsto (fun n => ∫ z in closedBall x r, mollify (heta (σ n)) w z * φ z)
        atTop (𝓝 (∫ z in closedBall x r, w z * φ z)) := by
    have h := setIntegral_mul_tendsto ((hconv w).comp hσ.tendsto_atTop)
      (φ.memLp 2 volume) (closedBall x r)
    apply h.congr
    intro n
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (mollifyL2_ae_eq (heta (σ n)) w)] with z hz
    change mollifyL2 (heta (σ n)) w z * φ z = _
    rw [hz]
  have hleft := (hpair (d i) test).add (hpair u (∂_{b} test))
  have hsum (n : ℕ) :
      (∫ z in closedBall x r, mollify (heta (σ n)) (d i) z * test z) +
        (∫ z in closedBall x r, mollify (heta (σ n)) u z * (∂_{b} test) z) =
        r * ∫ θ in (-Real.pi)..Real.pi,
          f (σ n) (polarPlane x (r, θ)) * test (polarPlane x (r, θ)) *
            Proofs.M58.angularPoint θ i := by
    have hm (w : Lp ℝ 2 (volume : Measure LoopPlane)) :
        MemLp (mollify (heta (σ n)) w) 2 volume :=
      (Lp.memLp (mollifyL2 (heta (σ n)) w)).ae_eq (mollifyL2_ae_eq (heta (σ n)) w)
    have h1 : IntegrableOn (fun z => mollify (heta (σ n)) (d i) z * test z)
        (closedBall x r) := ((hm (d i)).integrable_mul (test.memLp 2 volume)).integrableOn
    have h2 : IntegrableOn (fun z => mollify (heta (σ n)) u z * (∂_{b} test) z)
        (closedBall x r) := ((hm u).integrable_mul ((∂_{b} test).memLp 2 volume)).integrableOn
    rw [← integral_add h1 h2]
    have hg := smooth_disk_green (f (σ n))
      ((contDiff_mollify (heta (σ n)) u).of_le (by simp)) test i x
      (hε.trans_le hrange.1)
    simpa only [f, b, fderiv_mollify_of_weak_pairing (heta (σ n)) u (d i)
      (EuclideanSpace.basisFun (Fin 2) ℝ i) (hweak i),
      SchwartzMap.lineDerivOp_apply_eq_fderiv] using hg
  have heq := tendsto_nhds_unique hleft (hboundary.congr (fun n => (hsum n).symm))
  have h1 : IntegrableOn (fun z => d i z * test z) (closedBall x r) :=
    ((Lp.memLp (d i)).integrable_mul (test.memLp 2 volume)).integrableOn
  have h2 : IntegrableOn (fun z => u z * (∂_{b} test) z) (closedBall x r) :=
    ((Lp.memLp u).integrable_mul ((∂_{b} test).memLp 2 volume)).integrableOn
  rw [← integral_add h1 h2] at heq
  simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using heq

end PoincareConjecture.M65Interior
