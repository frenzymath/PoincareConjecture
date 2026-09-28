import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.CanonicalRampInitialFamilyJets
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.CanonicalRampLength
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceGaugeCurvatureLp
import PoincareConjecture.Proofs.M63.Sec19_3_Ramps.RampInitialBounds
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicSmoothApproximation
import PoincareConjecture.Proofs.M58.Cor18_28_PeriodicSpeed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M63

open Proofs.M58

theorem exists_canonicalRamp_initial_family_bounds
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {a b : ℝ} (F : RicciFlow 3 M (Icc a b))
    (hcompact : IsCompact (univ : Set M))
    {Gamma : C(LoopTwoSphere, C1FreeLoopSpace (M := M))} {zeta : ℝ}
    (A : M63RawApproximation F Gamma zeta) {circumference : ℝ}
    (P : M62.CircleProductData F circumference) :
    let c0 : LoopTwoSphere → ℝ → ℝ → P.charts.Point :=
      fun z x _ => m63CanonicalRamp P (periodicFreeLoop (A.family z)) x
    ∃ nu0 V0 B0 m R0 : ℝ,
      0 < nu0 ∧ 0 ≤ V0 ∧ 0 ≤ B0 ∧ 0 < m ∧ 0 ≤ R0 ∧
        ∀ z x,
          nu0 ≤ curveSpeed P.flow (c0 z) a x ∧
          curveSpeed P.flow (c0 z) a x ≤ V0 ∧
          |deriv (curveSpeed P.flow (c0 z) a) x| ≤ B0 ∧
          m ≤ m62Slope P (c0 z) a x ∧
          m63RampRatio P (c0 z) 1 a x ≤ R0 := by
  classical
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  let z0 : LoopTwoSphere := ⟨EuclideanSpace.single (0 : Fin 3) 1, by simp⟩
  let : Nonempty M := ⟨periodicFreeLoop (A.family z0) 0⟩
  let sphereHomeo : Metric.sphere (0 : LoopAmbient) 1 ≃ₜ LoopTwoSphere :=
    Homeomorph.setCongr (by ext z; exact mem_sphere_zero_iff_norm)
  let : CompactSpace LoopTwoSphere := sphereHomeo.compactSpace
  let gamma : LoopTwoSphere → ℝ → P.charts.Point :=
    fun z => m63CanonicalRamp P (periodicFreeLoop (A.family z))
  let c0 : LoopTwoSphere → ℝ → ℝ → P.charts.Point := fun z x _ => gamma z x
  let kappa := circumference / curvePeriod
  have hkappa : 0 < kappa := div_pos P.circle.positive Real.two_pi_pos
  have hab : a < b := by
    obtain ⟨s, hs, t, ht, hne⟩ := F.nontrivial
    by_contra! h
    apply hne
    linarith [hs.1, hs.2, ht.1, ht.2]
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hgamma (z : LoopTwoSphere) : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (3 + 1)) ∞ (gamma z) :=
    canonicalRamp_contMDiff P le_rfl (A.angular_smooth z)
  have himm (z : LoopTwoSphere) (x : ℝ) :
      curveVelocity (n := 3 + 1) (gamma z) x ≠ 0 :=
    ramp_immersed P (canonicalRamp_isRamp P
      ((A.angular_smooth z).mdifferentiable (by simp)) a) x
  obtain ⟨N, e, he, heClosed, heInjective⟩ :=
    exists_embedding_euclidean_of_compact (I := 𝓡 (3 + 1)) (M := P.charts.Point)
  obtain ⟨U, rho, hU, heU, hrho, hrhoe, _hmin, _hunique⟩ :=
    exists_smooth_compact_embedded_retraction e heClosed he heInjective
  let W := EuclideanSpace ℝ (Fin N)
  let f : LoopTwoSphere → ℝ → W := fun z x => e (gamma z x)
  let p : LoopTwoSphere → ℝ → W := fun z => deriv (f z)
  let q : LoopTwoSphere → ℝ → W := fun z => deriv (p z)
  let v : LoopTwoSphere → ℝ → ℝ := fun z => curveSpeed P.flow (c0 z) a
  obtain ⟨hf0, hf1, hf2⟩ := continuous_canonicalRamp_embedded_initial_jets F hcompact A P he
  have hf (z : LoopTwoSphere) : ContDiff ℝ 2 (f z) :=
    ((he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp
      ((hgamma z).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))).contDiff
  have hfd (z : LoopTwoSphere) (x : ℝ) : HasDerivAt (f z) (p z x) x :=
    ((hf z).differentiable (by norm_num) x).hasDerivAt
  have hpd (z : LoopTwoSphere) (x : ℝ) : HasDerivAt (p z) (q z x) x :=
    (((hf z).deriv' (n := 1)).differentiable (by norm_num) x).hasDerivAt
  have hvlow (z : LoopTwoSphere) (x : ℝ) : kappa ≤ v z x := by
    change kappa ≤ curveSpeed P.flow
      (fun y _ => m63CanonicalRamp P (periodicFreeLoop (A.family z)) y) a x
    rw [canonicalRamp_speed P ((A.angular_smooth z).mdifferentiableAt (by simp))]
    calc
      kappa = Real.sqrt (kappa ^ 2) := (Real.sqrt_sq hkappa.le).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by
        dsimp only [kappa]
        linarith [sq_nonneg (curveSpeed F
          (fun y _ => periodicFreeLoop (A.family z) y) a x)])
  have hvpos (z : LoopTwoSphere) (x : ℝ) : 0 < v z x := hkappa.trans_le (hvlow z x)
  have hpush (z : LoopTwoSphere) (x : ℝ) : p z x =
      (mfderiv (𝓡 (3 + 1)) 𝓘(ℝ, W) e (gamma z x)
        (curveVelocity (n := 3 + 1) (gamma z) x) : W) := by
    have hchain : fderiv ℝ (f z) x =
        (mfderiv (𝓡 (3 + 1)) 𝓘(ℝ, W) e (gamma z x)).comp
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 (3 + 1)) (gamma z) x) := by
      rw [← mfderiv_eq_fderiv]
      exact mfderiv_comp x (he.mdifferentiable (by simp)).mdifferentiableAt
        ((hgamma z).mdifferentiableAt (by simp))
    exact congrArg (fun L : ℝ →L[ℝ] W => L 1) hchain
  have hleft := (smooth_retraction_differentials he hU heU hrho hrhoe).2.2
  have hreturn (z : LoopTwoSphere) (x : ℝ) :
      mfderiv 𝓘(ℝ, W) (𝓡 (3 + 1)) rho (f z x) (p z x) =
        curveVelocity (n := 3 + 1) (gamma z) x := by
    dsimp only [f]
    rw [hpush]
    exact hleft (gamma z x) (curveVelocity (n := 3 + 1) (gamma z) x)
  let O : Set (W × W) := U ×ˢ univ
  have hO : IsOpen O := hU.prod isOpen_univ
  let B : W × W → ℝ := fun z => (P.flow.metric a).inner (rho z.1)
    (mfderiv 𝓘(ℝ, W) (𝓡 (3 + 1)) rho z.1 z.2)
    (mfderiv 𝓘(ℝ, W) (𝓡 (3 + 1)) rho z.1 z.2)
  have hmetric := (flow_pullback_metric_hessian_contDiffOn P.flow hU hrho
    (f := fun _ => 0) contMDiff_const).1
  have hB : ContDiffOn ℝ ∞ B O :=
    hmetric.comp (s := O)
      ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd).contDiffOn
      (fun z hz => ⟨⟨ha, hz.1⟩, hz.2⟩)
  have hBvalue (z : LoopTwoSphere) (x : ℝ) : B (f z x, p z x) =
      (P.flow.metric a).inner (gamma z x)
        (curveVelocity (n := 3 + 1) (gamma z) x)
        (curveVelocity (n := 3 + 1) (gamma z) x) := by
    dsimp only [B, f]
    rw [hpush]
    erw [hleft (gamma z x) (curveVelocity (n := 3 + 1) (gamma z) x), hrhoe (gamma z x)]
  have hBpos (z : LoopTwoSphere) (x : ℝ) : 0 < B (f z x, p z x) := by
    rw [hBvalue]
    exact (P.flow.metric a).pos _ _ (himm z x)
  have hvvalue (z : LoopTwoSphere) (x : ℝ) : v z x = Real.sqrt (B (f z x, p z x)) := by
    rw [hBvalue]
    rfl
  let input : LoopTwoSphere × ℝ → W × W := fun z => (f z.1 z.2, p z.1 z.2)
  have hinput : Continuous input := hf0.prodMk hf1
  have hmem (z : LoopTwoSphere × ℝ) : input z ∈ O :=
    ⟨heU (mem_range_self _), mem_univ _⟩
  have hvc : Continuous (fun z : LoopTwoSphere × ℝ => v z.1 z.2) :=
    (Real.continuous_sqrt.comp (hB.continuousOn.comp_continuous
      (f := input) hinput hmem)).congr (fun z => (hvvalue z.1 z.2).symm)
  have hDB : ContinuousOn (fderiv ℝ B) O :=
    hB.continuousOn_fderiv_of_isOpen hO (by simp)
  let g : LoopTwoSphere → ℝ → ℝ := fun z x =>
    fderiv ℝ B (f z x, p z x) (p z x, q z x) / (2 * v z x)
  have hgc : Continuous (fun z : LoopTwoSphere × ℝ => g z.1 z.2) :=
    ((hDB.comp_continuous (f := input) hinput hmem).clm_apply (hf1.prodMk hf2)).div
      (continuous_const.mul hvc) (fun z => mul_ne_zero (by norm_num) (hvpos z.1 z.2).ne')
  have hgd (z : LoopTwoSphere) (x : ℝ) : HasDerivAt (v z) (g z x) x := by
    have hd := ((hB.contDiffAt (hO.mem_nhds (hmem (z, x)))).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt x ((hfd z x).prodMk (hpd z x))
    have hs : HasDerivAt (v z)
        (fderiv ℝ B (f z x, p z x) (p z x, q z x) /
          (2 * Real.sqrt (B (f z x, p z x)))) x :=
      (hd.sqrt (hBpos z x).ne').congr_of_eventuallyEq
        (Eventually.of_forall (hvvalue z))
    simpa only [g, hvvalue z x] using hs
  let Omega : Set (W × W) :=
    {z | z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 (3 + 1)) rho z.1 z.2 ≠ 0}
  let alpha := fun z : W × W => ambientCurvePrincipal P.flow rho a z.1 z.2
  let beta := fun z : W × W => ambientCurveLower P.flow e rho a z.1 z.2
  let lam : W × W → W →L[ℝ] ℝ := fun z => (1 / 2 : ℝ) •
    (fderiv ℝ alpha z).comp (ContinuousLinearMap.inr ℝ W W)
  let eta := fun z : W × W => fderiv ℝ alpha z (z.2, 0) / 2
  let C : W × W → W →L[ℝ] W :=
    fun z => alpha z • ContinuousLinearMap.id ℝ W + (lam z).smulRight z.2
  let d : W × W → W := fun z => beta z + eta z • z.2
  obtain ⟨_hLam, _hEta, hC, hd, hformula⟩ :=
    ambientCurve_curvature_label_affine P.flow he hU heU hrho hrhoe ha
  let D : Set ((W × W) × W) := {z | z.1 ∈ Omega}
  let Hbar : (W × W) × W → W := fun z => C z.1 z.2 + d z.1
  let Q : (W × W) × W → ℝ := fun z => B (z.1.1, Hbar z)
  have hHbar : ContinuousOn Hbar D :=
    ((hC.comp continuous_fst.continuousOn (fun _ hz => hz)).clm_apply
      continuousOn_snd).add (hd.comp continuous_fst.continuousOn (fun _ hz => hz))
  have hQ : ContinuousOn Q D :=
    hB.continuousOn.comp (continuousOn_fst.fst.prodMk hHbar)
      (fun _ hz => ⟨hz.1, mem_univ _⟩)
  have hguard (z : LoopTwoSphere) (x : ℝ) : (f z x, p z x) ∈ Omega := by
    refine ⟨heU (mem_range_self _), ?_⟩
    rw [hreturn]
    exact himm z x
  have hfixed (z : LoopTwoSphere) (x : ℝ) : f z x = e (rho (f z x)) := by
    dsimp only [f]
    rw [hrhoe]
  let k : LoopTwoSphere → ℝ → ℝ := fun z x => Q ((f z x, p z x), q z x)
  have hkc : Continuous (fun z : LoopTwoSphere × ℝ => k z.1 z.2) :=
    hQ.comp_continuous ((hf0.prodMk hf1).prodMk hf2) (fun z => hguard z.1 z.2)
  have hkvalue (z : LoopTwoSphere) (x : ℝ) :
      k z x = m62CurvatureSquared P.flow (c0 z) a x := by
    have hcurv := (hformula (f z) (hf z) (hguard z) (hfixed z) x).2
    have hback : mfderiv 𝓘(ℝ, W) (𝓡 (3 + 1)) rho (f z x)
        (mfderiv (𝓡 (3 + 1)) 𝓘(ℝ, W) e (rho (f z x))
          (m62CurvatureVector P.flow (fun y (_ : ℝ) => rho (f z y)) a x)) =
        m62CurvatureVector P.flow (fun y (_ : ℝ) => rho (f z y)) a x := by
      let drho : W → W →L[ℝ] EuclideanSpace ℝ (Fin (3 + 1)) :=
        fun w => mfderiv 𝓘(ℝ, W) (𝓡 (3 + 1)) rho w
      have heq : drho (f z x) = drho (e (rho (f z x))) :=
        congrArg drho (hfixed z x)
      change drho (f z x) _ = _
      rw [heq]
      exact hleft (rho (f z x))
        (m62CurvatureVector P.flow (fun y (_ : ℝ) => rho (f z y)) a x)
    change (P.flow.metric a).inner (rho (f z x))
      (mfderiv 𝓘(ℝ, W) (𝓡 (3 + 1)) rho (f z x)
        (C (f z x, p z x) (q z x) + d (f z x, p z x)))
      (mfderiv 𝓘(ℝ, W) (𝓡 (3 + 1)) rho (f z x)
        (C (f z x, p z x) (q z x) + d (f z x, p z x))) = _
    rw [← hcurv, hback]
    change m62CurvatureSquared P.flow (fun y (_ : ℝ) => rho (f z y)) a x = _
    rw [show (fun y (_ : ℝ) => rho (f z y)) = c0 z from
      funext (fun y => funext (fun _ => hrhoe (gamma z y)))]
  have hfper (z : LoopTwoSphere) : Function.Periodic (f z) curvePeriod :=
    fun x => congrArg e (canonicalRamp_periodic P (periodic_periodicFreeLoop (A.family z)) x)
  have hpper (z : LoopTwoSphere) : Function.Periodic (p z) curvePeriod :=
    (hfper z).deriv_of_differentiable ((hf z).differentiable (by norm_num))
  have hqper (z : LoopTwoSphere) : Function.Periodic (q z) curvePeriod :=
    (hpper z).deriv_of_differentiable (((hf z).deriv' (n := 1)).differentiable (by norm_num))
  have hvper (z : LoopTwoSphere) : Function.Periodic (v z) curvePeriod := by
    intro x
    rw [hvvalue z (x + curvePeriod), hvvalue z x, hfper z x, hpper z x]
  have hgper (z : LoopTwoSphere) : Function.Periodic (g z) curvePeriod := by
    have h := (hvper z).deriv_of_differentiable (fun x => (hgd z x).differentiableAt)
    rwa [show deriv (v z) = g z from funext (fun x => (hgd z x).deriv)] at h
  have hkper (z : LoopTwoSphere) : Function.Periodic (k z) curvePeriod := by
    intro x
    dsimp only [k]
    rw [hfper z x, hpper z x, hqper z x]
  have bound (w : LoopTwoSphere → ℝ → ℝ)
      (hw : Continuous (fun z : LoopTwoSphere × ℝ => w z.1 z.2))
      (hper : ∀ z, Function.Periodic (w z) curvePeriod) :
      ∃ B0 : ℝ, 0 ≤ B0 ∧ ∀ z x, w z x ≤ B0 := by
    obtain ⟨B0, hB0⟩ := (isCompact_univ.prod (isCompact_Icc :
      IsCompact (Icc (0 : ℝ) curvePeriod))).bddAbove_image hw.continuousOn
    refine ⟨max 0 B0, le_max_left _ _, ?_⟩
    intro z x
    obtain ⟨y, hy, hxy⟩ := (hper z).exists_mem_Ico₀ Real.two_pi_pos x
    rw [hxy]
    exact (hB0 ⟨(z, y), ⟨mem_univ _, Ico_subset_Icc_self hy⟩, rfl⟩).trans
      (le_max_right _ _)
  obtain ⟨Bv, _hBv, hBv⟩ := bound v hvc hvper
  obtain ⟨Bg, hBg, hBgBound⟩ := bound (fun z x => |g z x|) hgc.abs
    (fun z x => congrArg abs (hgper z x))
  obtain ⟨Q0, _hQ0, hQBound⟩ := bound k hkc hkper
  let V0 := max 1 Bv
  have hV0 : 0 < V0 := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hvupper (z : LoopTwoSphere) (x : ℝ) : v z x ≤ V0 :=
    (hBv z x).trans (le_max_right _ _)
  let m := kappa / V0
  have hm : 0 < m := div_pos hkappa hV0
  have hslope (z : LoopTwoSphere) (x : ℝ) : m62Slope P (c0 z) a x = kappa / v z x := by
    let phi : ℝ → ℝ := fun y => circumference * y / curvePeriod
    have hphi : Differentiable ℝ phi :=
      ((differentiable_const circumference).mul differentiable_id).div_const _
    have hdphi : HasDerivAt phi kappa x := by
      simpa +instances only [phi, kappa, mul_one] using!
        ((hasDerivAt_id x).const_mul circumference).div_const curvePeriod
    rw [m63Slope_eq_lift_deriv_div_speed P
      ((hgamma z).mdifferentiable (by simp)) hphi (fun _ => rfl), hdphi.deriv]
  have hslopeLow (z : LoopTwoSphere) (x : ℝ) : m ≤ m62Slope P (c0 z) a x := by
    rw [hslope]
    exact div_le_div_of_nonneg_left hkappa.le (hvpos z x) (hvupper z x)
  let R0 := Real.sqrt (Q0 + 1) / m
  have hR0 : 0 ≤ R0 := div_nonneg (Real.sqrt_nonneg _) hm.le
  refine ⟨kappa, V0, Bg, m, R0, hkappa, hV0.le, hBg, hm, hR0, ?_⟩
  intro z x
  refine ⟨hvlow z x, hvupper z x, ?_, hslopeLow z x, ?_⟩
  · rw [(hgd z x).deriv]
    exact hBgBound z x
  · have hnum : m62RegularizedCurvature P.flow (c0 z) 1 a x ≤ Real.sqrt (Q0 + 1) := by
      change Real.sqrt (m62CurvatureSquared P.flow (c0 z) a x + 1 ^ 2) ≤ _
      rw [one_pow, ← hkvalue]
      exact Real.sqrt_le_sqrt (add_le_add (hQBound z x) le_rfl)
    have hu : 0 < m62Slope P (c0 z) a x := hm.trans_le (hslopeLow z x)
    exact (div_le_div_of_nonneg_right hnum hu.le).trans
      (div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hm (hslopeLow z x))

end PoincareConjecture.M63
