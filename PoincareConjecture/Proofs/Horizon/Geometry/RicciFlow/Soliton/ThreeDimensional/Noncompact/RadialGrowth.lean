import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.RicciIntegral
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Regularity.Euclidean
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Regularity.Pullback
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Hessian.Chart
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.Geodesic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.NormBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle

noncomputable section

namespace PoincareConjecture.GradientShrinkingSolitonData

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

private theorem hessian_in_chart_of_C2 {g : RiemannianMetric 3 M}
    (D : LeviCivitaData g) {f : M → ℝ} (a : M)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ (extChartAt (𝓡 3) a).target)
    (hf : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) 2 f ((extChartAt (𝓡 3) a).symm x))
    (v w : EuclideanSpace ℝ (Fin 3)) :
    D.hessian f ((extChartAt (𝓡 3) a).symm x)
        (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) a).symm x v)
        (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) a).symm x w) =
      fderiv ℝ (fderiv ℝ (f ∘ (extChartAt (𝓡 3) a).symm)) x v w -
        fderiv ℝ (f ∘ (extChartAt (𝓡 3) a).symm) x
          (CoordinateExponential.christoffelBilinear
            (g.pullbackCoefficients (extChartAt (𝓡 3) a).symm) x v w) := by
  let c := extChartAt (𝓡 3) a
  have hc (y : EuclideanSpace ℝ (Fin 3)) (hy : y ∈ c.target) :
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm y :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) a hy).contMDiffAt
      (extChartAt_target_mem_nhds' hy)
  have hi (y : EuclideanSpace ℝ (Fin 3)) (hy : y ∈ c.target) :
      (mfderiv (𝓡 3) (𝓡 3) c.symm y).IsInvertible := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm hy
  obtain ⟨gE, DE, V, hVo, hxV, _, hE⟩ :=
    RiemannianMetric.exists_local_realization (isOpen_extChartAt_target a) hx
      (g.pullbackCoefficients c.symm) (g.contDiffOn_chartCoefficients a)
      (fun y _ b d => g.symm _ _ _)
      (fun y hy b hb => by
        apply g.pos (c.symm y)
        intro hzero
        apply hb
        apply (hi y hy).injective
        rw [map_zero]
        exact hzero)
  have heq : gE.euclideanCoefficients =ᶠ[𝓝 x] g.pullbackCoefficients c.symm := by
    filter_upwards [hVo.mem_nhds hxV] with y hy
    exact hE y hy
  have hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 3) (𝓡 3) c.symm y).IsInvertible :=
    Filter.mem_of_superset (extChartAt_target_mem_nhds' hx) hi
  have hmetric : ∀ᶠ y in 𝓝 x, ∀ b d : EuclideanSpace ℝ (Fin 3),
      gE.inner y b d = g.inner (c.symm y)
        (mfderiv (𝓡 3) (𝓡 3) c.symm y b) (mfderiv (𝓡 3) (𝓡 3) c.symm y d) := by
    filter_upwards [heq] with y hy b d
    exact congrArg (fun B => B b d) hy
  have hΓ : CoordinateExponential.christoffelBilinear gE.euclideanCoefficients x =
      CoordinateExponential.christoffelBilinear (g.pullbackCoefficients c.symm) x := by
    simp only [CoordinateExponential.christoffelBilinear, heq.self_of_nhds, heq.fderiv_eq]
  rw [← DE.hessian_comp_of_metric_pullback_of_C2 D (hc x hx) hinv hmetric hf,
    DE.hessian_eq_fderiv_sub_connectionCoefficient_of_C2
      (contMDiffAt_iff_contDiffAt.mp (hf.comp x ((hc x hx).of_le (by norm_cast)))),
    DE.connectionCoefficient_eq_coordinateChristoffel,
    ← CoordinateExponential.christoffelBilinear_apply, hΓ]

private theorem hasDerivAt_deriv_potential_geodesic {g : RiemannianMetric 3 M}
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) 2 f)
    {γ : ℝ → M} {I : Set ℝ} (hγ : g.IsGeodesicOn γ I)
    {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (deriv (f ∘ γ))
      (D.hessian f (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1)) t := by
  obtain ⟨p, q, w, hlocal⟩ := hγ t ht
  let c := extChartAt (𝓡 3) p
  let F := f ∘ c.symm
  have hF (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ c.target) :
      ContDiffAt ℝ 2 F x := by
    apply contMDiffAt_iff_contDiffAt.mp
    exact (hf (c.symm x)).comp x
      (((contMDiffWithinAt_extChartAt_symm_target (n := ∞) p hx).contMDiffAt
        (extChartAt_target_mem_nhds' hx)).of_le (by norm_cast))
  have hfirst : ∀ᶠ u in 𝓝 t,
      HasDerivAt (f ∘ γ) (fderiv ℝ F (q u) (w u)) u := by
    filter_upwards [hlocal, hlocal.eventually_nhds] with u hu hue
    have hd := ((hF (q u) hu.2.1).differentiableAt (by norm_num)).hasFDerivAt
      |>.comp_hasDerivAt u hu.2.2.1
    apply hd.congr_of_eventuallyEq
    filter_upwards [hue] with v hv
    exact congrArg f hv.1
  have hqt := hlocal.self_of_nhds
  have hsecond := (((hF (q t) hqt.2.1).fderiv_right (m := 1)
    (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t hqt.2.2.1
  have hfield := hsecond.clm_apply hqt.2.2.2
  have hH := hessian_in_chart_of_C2 D p hqt.2.1 (hf _) (w t) (w t)
  have hfieldH : HasDerivAt (deriv (f ∘ γ))
      (D.hessian f (c.symm (q t))
        (mfderiv (𝓡 3) (𝓡 3) c.symm (q t) (w t))
        (mfderiv (𝓡 3) (𝓡 3) c.symm (q t) (w t))) t := by
    rw [hH]
    have hd : HasDerivAt (fun u => fderiv ℝ F (q u) (w u))
        (fderiv ℝ (fderiv ℝ F) (q t) (w t) (w t) -
          fderiv ℝ F (q t)
            (CoordinateExponential.christoffelBilinear
              (g.pullbackCoefficients c.symm) (q t) (w t) (w t))) t := by
      simpa +instances only [Function.comp_def, map_neg, ← sub_eq_add_neg,
        CoordinateExponential.christoffelBilinear_apply] using hfield
    exact hd.congr_of_eventuallyEq (hfirst.mono fun _ hu => hu.deriv)
  have hcurve : γ =ᶠ[𝓝 t] fun u => c.symm (q u) := hlocal.mono fun _ hu => hu.1
  have hc := ((contMDiffWithinAt_extChartAt_symm_target (n := ∞) p hqt.2.1).contMDiffAt
    (extChartAt_target_mem_nhds' hqt.2.1)).mdifferentiableAt (by simp)
  have hv := congrArg (fun A => A (1 : ℝ))
    (mfderiv_comp t hc hqt.2.2.1.differentiableAt.mdifferentiableAt)
  rw [mfderiv_eq_fderiv] at hv
  change mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun u => c.symm (q u)) t 1 =
    mfderiv (𝓡 3) (𝓡 3) c.symm (q t) (deriv q t) at hv
  rw [hqt.2.2.1.deriv] at hv
  rw [hcurve.mfderiv_eq, hcurve.self_of_nhds, hv]
  exact hfieldH

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem exists_radial_derivative_lower_bound
    (S : GradientShrinkingSolitonData 3 M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ → M) (I : Set ℝ) (L : ℝ),
      IsOpen I → Icc 0 L ⊆ I → S.metric.IsGeodesicOn γ I → 0 ≤ L →
      (∀ s ∈ Icc 0 L, S.metric.tangentNorm (γ s)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ s 1) = 1) →
      S.metric.edist (γ 0) (γ L) = ENNReal.ofReal L →
      deriv (S.potential ∘ γ) 0 + L / 2 - C ≤ deriv (S.potential ∘ γ) L := by
  obtain ⟨K, hK, hRm⟩ := S.bounded_curvature
  let B : ℝ := 27 * K
  refine ⟨6 + 4 * B, by dsimp [B]; positivity, ?_⟩
  intro γ I L hI hsub hgeo hL hspeed hmin
  let v := fun s => mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ s 1
  let q := deriv (S.potential ∘ γ)
  let r := fun s => S.connection.ricci (γ s) (v s) (v s)
  have hunit (s : ℝ) (hs : s ∈ Icc 0 L) : S.metric.inner (γ s) (v s) (v s) = 1 := by
    have hn : 0 ≤ S.metric.inner (γ s) (v s) (v s) := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
        ⟨S.metric.toRiemannianMetric⟩
      change 0 ≤ inner ℝ (v s) (v s)
      exact real_inner_self_nonneg
    have h := Real.sq_sqrt hn
    change (S.metric.tangentNorm (γ s) (v s)) ^ 2 = _ at h
    rw [hspeed s hs] at h
    norm_num at h ⊢
    exact h.symm
  have hd (s : ℝ) (hs : s ∈ Icc 0 L) : HasDerivAt q ((1 / 2 : ℝ) - r s) s := by
    have heq := S.soliton_equation (γ s) (v s) (v s)
    rw [hunit s hs, mul_one] at heq
    convert hasDerivAt_deriv_potential_geodesic S.connection S.potential_C2 hgeo
      (hsub hs) using 1
    dsimp only [r]
    linarith
  have hqc : ContinuousOn q (Icc 0 L) :=
    fun s hs => (hd s hs).continuousAt.continuousWithinAt
  have hF (s : ℝ) (hs : s ∈ I) : ContDiffAt ℝ 2 (S.potential ∘ γ) s :=
    contMDiffAt_iff_contDiffAt.mp ((S.potential_C2 _).comp s
      ((Conjugate.Realization.contMDiffAt_of_isGeodesicOn hgeo hs).of_le (by norm_cast)))
  have hrc : ContinuousOn r (Icc 0 L) := by
    have hder : ContinuousOn (deriv q) (Icc 0 L) := by
      intro s hs
      have hdq : ContDiffAt ℝ 1 q s :=
        (hF s (hsub hs)).derivWithin (m := 1) (by norm_num)
      exact (hdq.derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
    apply ((continuousOn_const (c := (1 / 2 : ℝ))).sub hder).congr
    intro s hs
    change r s = (1 / 2 : ℝ) - deriv q s
    rw [(hd s hs).deriv]
    ring
  have hri : IntervalIntegrable r volume 0 L := hrc.intervalIntegrable_of_Icc hL
  have hFTC : (∫ s in (0 : ℝ)..L, (1 / 2 : ℝ) - r s) = q L - q 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hL hqc
      (fun s hs => hd s (Ioo_subset_Icc_self hs))
      (intervalIntegrable_const.sub hri)
  have hRic (s : ℝ) (hs : s ∈ Icc 0 L) : r s ≤ B := by
    have h := S.connection.abs_ricci_quadratic_le_curvatureTensorNorm (γ s) (v s)
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) (γ s)) = 3 := finrank_euclideanSpace_fin
    simp only [Fintype.card_fin, hdim, Nat.cast_ofNat, hunit s hs, mul_one] at h
    dsimp only [r, B]
    nlinarith [le_abs_self (S.connection.ricci (γ s) (v s) (v s)),
      le_abs_self (S.connection.curvatureTensorNorm (γ s)), hRm (γ s)]
  have hInt := S.connection.integral_ricci_le_of_minimizing hI hsub hgeo hL hspeed hmin
    (show 0 ≤ B by dsimp [B]; positivity) (by norm_num : (0 : ℝ) < 1) hRic
  rw [intervalIntegral.integral_sub intervalIntegrable_const hri,
    intervalIntegral.integral_const] at hFTC
  simp only [sub_zero, smul_eq_mul] at hFTC
  change q 0 + L / 2 - (6 + 4 * B) ≤ q L
  dsimp only [r, v] at hFTC
  norm_num at hInt
  linarith

end PoincareConjecture.GradientShrinkingSolitonData
