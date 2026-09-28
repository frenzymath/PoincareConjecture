import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Flow.ManifoldExpansion
import Mathlib.Analysis.Calculus.ImplicitContDiff

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

private theorem exists_smooth_scalar_implicit_function
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : E × ℝ → ℝ} {U : Set (E × ℝ)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) {p : E × ℝ} (hp : p ∈ U)
    (hinv : ((fderiv ℝ F p).comp (ContinuousLinearMap.inr ℝ E ℝ)).IsInvertible) :
    ∃ (V : Set E) (ψ : E → ℝ), IsOpen V ∧ p.1 ∈ V ∧
      ContDiffOn ℝ ∞ ψ V ∧ ψ p.1 = p.2 ∧
      ∀ z ∈ V, (z, ψ z) ∈ U ∧ F (z, ψ z) = F p := by
  have hFp := hF.contDiffAt (hU.mem_nhds hp)
  let d := (hFp.hasStrictFDerivAt (by simp)).implicitFunctionDataOfProdDomain hinv
  let G := d.prodFun
  let e₀ := d.toOpenPartialHomeomorph
  have hG : ContDiffOn ℝ ∞ G U := hF.prodMk contDiff_fst.contDiffOn
  have hGinv : (fderiv ℝ G p).IsInvertible := d.isInvertible_fderiv_prodFun
  let W := U ∩ (fderiv ℝ G) ⁻¹' range
    ((↑) : ((E × ℝ) ≃L[ℝ] (ℝ × E)) → (E × ℝ) →L[ℝ] (ℝ × E))
  have hW : IsOpen W :=
    (hG.continuousOn_fderiv_of_isOpen hU (by simp)).isOpen_inter_preimage
      hU ContinuousLinearEquiv.isOpen
  have hpW : p ∈ W := ⟨hp, hGinv⟩
  let e := e₀.restrOpen W hW
  have hpes : p ∈ e.source := ⟨d.pt_mem_toOpenPartialHomeomorph_source, hpW⟩
  have hes : e.source ⊆ U := fun z hz => hz.2.1
  have hecoe : (e : E × ℝ → ℝ × E) = G := rfl
  have heinv : ContDiffOn ℝ ∞ e.symm e.target := by
    intro z hz
    have hzs := e.map_target hz
    obtain ⟨A, hA⟩ := hzs.2.2
    have hGA := hG.contDiffAt (hU.mem_nhds (hes hzs))
    apply (e.contDiffAt_symm hz (f₀' := A) ?_ ?_).contDiffWithinAt
    · rw [hecoe, hA]
      exact (hGA.differentiableAt (by simp)).hasFDerivAt
    · rw [hecoe]
      exact hGA
  let V := (fun z : E => (F p, z)) ⁻¹' e.target
  let ψ : E → ℝ := fun z => (e.symm (F p, z)).2
  have hV : IsOpen V := e.open_target.preimage (continuous_const.prodMk continuous_id)
  have hpV : p.1 ∈ V := e.map_source hpes
  have hψ : ContDiffOn ℝ ∞ ψ V :=
    (heinv.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (show MapsTo (fun z : E => (F p, z)) V e.target from fun _ hz => hz)).snd
  refine ⟨V, ψ, hV, hpV, hψ, ?_, ?_⟩
  · exact congrArg Prod.snd (e.left_inv hpes)
  · intro z hz
    have he := e.right_inv hz
    have he₁ : F (e.symm (F p, z)) = F p := congrArg Prod.fst he
    have he₂ : (e.symm (F p, z)).1 = z := congrArg Prod.snd he
    have hpair : (z, ψ z) = e.symm (F p, z) := by
      exact Prod.ext he₂.symm rfl
    exact ⟨hpair ▸ hes (e.map_target hz), hpair ▸ he₁⟩

private theorem hitting_time_control
    {F : ℝ → ℝ} {F' : ℝ → ℝ} {δ c s : ℝ}
    (hδ : 0 < δ) (hc : 0 < c) (hs : s ∈ Ioo (-δ) δ)
    (hF : ∀ t ∈ Ioo (-δ) δ, HasDerivAt F (F' t) t)
    (hd : ∀ t ∈ Ioo (-δ) δ, F' t ≤ -c) :
    |s| ≤ |F 0 - F s| / c ∧ (0 ≤ s ↔ F s ≤ F 0) := by
  have hz : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have hcont : ContinuousOn F (Ioo (-δ) δ) := fun t ht =>
    (hF t ht).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ F (interior (Ioo (-δ) δ)) := by
    simpa only [interior_Ioo] using
      (show DifferentiableOn ℝ F (Ioo (-δ) δ) from fun t ht =>
        (hF t ht).differentiableAt.differentiableWithinAt)
  have hder : ∀ t ∈ interior (Ioo (-δ) δ), deriv F t ≤ -c := by
    simpa only [interior_Ioo] using
      (show ∀ t ∈ Ioo (-δ) δ, deriv F t ≤ -c from fun t ht => by
        rw [(hF t ht).deriv]; exact hd t ht)
  by_cases hpos : 0 ≤ s
  · have hle := (convex_Ioo (-δ) δ).image_sub_le_mul_sub_of_deriv_le
      hcont hdiff hder 0 hz s hs hpos
    have hval : F s ≤ F 0 := by nlinarith
    refine ⟨?_, iff_of_true hpos hval⟩
    rw [abs_of_nonneg hpos, abs_of_nonneg (sub_nonneg.mpr hval)]
    exact (le_div_iff₀ hc).mpr (by nlinarith)
  · have hneg : s < 0 := lt_of_not_ge hpos
    have hle := (convex_Ioo (-δ) δ).image_sub_le_mul_sub_of_deriv_le
      hcont hdiff hder s hs 0 hz hneg.le
    have hval : F 0 < F s := by nlinarith
    refine ⟨?_, iff_of_false hpos (not_le.mpr hval)⟩
    rw [abs_of_neg hneg, abs_of_neg (sub_neg.mpr hval)]
    exact (le_div_iff₀ hc).mpr (by nlinarith)

private theorem scalar_derivative_along_curve
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {f : M → ℝ} {γ : ℝ → M} {W : (y : M) → TangentSpace (𝓡 n) y} {s : ℝ}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f (γ s))
    (hγ : IsMIntegralCurveAt (I := 𝓡 n) γ W s) :
    HasDerivAt (fun t => f (γ t)) (mvfderiv (𝓡 n) f (γ s) (W (γ s))) s := by
  have hd := hf.hasMFDerivAt.comp s hγ.hasMFDerivAt
  have hd' := (hasMFDerivAt_iff_hasFDerivAt.mp hd).hasDerivAt
  change HasDerivAt (fun t => f (γ t))
    (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f (γ s) ((1 : ℝ) • W (γ s))) s at hd'
  simpa [mvfderiv, NormedSpace.fromTangentSpace] using hd'

end PoincareConjecture.LeviCivitaData

theorem PoincareConjecture.LeviCivitaData.exists_smooth_normalizedGradient_hitting_map
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : PoincareConjecture.RiemannianMetric n M} (D : PoincareConjecture.LeviCivitaData g)
    {f h : M → ℝ} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    (hh : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ h U)
    {l H c : ℝ} (hl : 0 < l) (hH : 0 ≤ H) (hc : 0 < c)
    (hgrad : ∀ y ∈ U, l ≤ g.tangentNorm y (D.gradient h y))
    (hhess : ∀ y ∈ U, ∀ v : TangentSpace (𝓡 n) y,
      mvfderiv (𝓡 n) h y v = 0 → D.hessian h y v v ≤ H * g.inner y v v)
    (hcross : ∀ y ∈ U, mvfderiv (𝓡 n) f y (D.normalizedGradient h y) ≤ -c)
    {x : M} (hx : x ∈ U) :
    ∃ (V : Set M) (ε δ : ℝ) (Φ : ℝ × M → M) (σ : ℝ × M → ℝ),
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ 0 < ε ∧ 0 < δ ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ Φ (Ioo (-δ) δ ×ˢ V) ∧
      (∀ y ∈ V, Φ (0, y) = y) ∧
      (∀ y ∈ V, (∀ s ∈ Ioo (-δ) δ, Φ (s, y) ∈ U) ∧
        IsMIntegralCurveOn (I := 𝓡 n) (fun s => Φ (s, y))
          (D.normalizedGradient h) (Ioo (-δ) δ)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ σ
        (Ioo (f x - ε) (f x + ε) ×ˢ V) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
        (fun p : ℝ × M => Φ (σ p, p.2)) (Ioo (f x - ε) (f x + ε) ×ˢ V) ∧
      (∀ t ∈ Ioo (f x - ε) (f x + ε), ∀ y ∈ V,
        σ (t, y) ∈ Ioo (-δ) δ ∧ f (Φ (σ (t, y), y)) = t ∧
          |σ (t, y)| ≤ |f y - t| / c ∧
          (0 ≤ σ (t, y) ↔ t ≤ f y) ∧
          (f y = t → Φ (σ (t, y), y) = y)) ∧
      ∀ y ∈ V, ∀ s ∈ Ico 0 δ,
        h (Φ (s, y)) = h y + s ∧
        ∀ v : TangentSpace (𝓡 n) y, mvfderiv (𝓡 n) h y v = 0 →
          g.inner (Φ (s, y)) (mfderiv (𝓡 n) (𝓡 n) (fun z => Φ (s, z)) y v)
            (mfderiv (𝓡 n) (𝓡 n) (fun z => Φ (s, z)) y v) ≤
          g.inner y v v * Real.exp (2 * (H / l ^ 2) * s) := by
  obtain ⟨W, δ, Φ, hWo, hxW, hWU, hδ, hΦ, hzero, horbit, hexp⟩ :=
    D.exists_local_normalizedGradient_manifoldFlow_with_expansion hU hh hl hH hgrad hhess hx
  have hzeroTime : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have hder (y : M) (hy : y ∈ W) (s : ℝ) (hs : s ∈ Ioo (-δ) δ) :
      HasDerivAt (fun t => f (Φ (t, y)))
        (mvfderiv (𝓡 n) f (Φ (s, y)) (D.normalizedGradient h (Φ (s, y)))) s :=
    scalar_derivative_along_curve
      ((hf.contMDiffAt (hU.mem_nhds ((horbit y hy).1 s hs))).mdifferentiableAt (by simp))
      ((horbit y hy).2.isMIntegralCurveAt (isOpen_Ioo.mem_nhds hs))
  let e := extChartAt (𝓡 n) x
  have he (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ e.target) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ e.symm z :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) x hz).contMDiffAt
      (extChartAt_target_mem_nhds' hz)
  let A := e.target ∩ e.symm ⁻¹' W
  have hAo : IsOpen A :=
    (show ContinuousOn e.symm e.target from fun z hz =>
      (he z hz).continuousAt.continuousWithinAt).isOpen_inter_preimage
        (isOpen_extChartAt_target x) hWo
  have hxA : e x ∈ A := ⟨mem_extChartAt_target x, by
    change e.symm (e x) ∈ W
    simpa only [e.left_inv (mem_extChartAt_source x)] using hxW⟩
  let F : (ℝ × EuclideanSpace ℝ (Fin n)) × ℝ → ℝ :=
    fun q => f (Φ (q.2, e.symm q.1.2)) - q.1.1
  let O : Set ((ℝ × EuclideanSpace ℝ (Fin n)) × ℝ) := (univ ×ˢ A) ×ˢ Ioo (-δ) δ
  have hOo : IsOpen O := (isOpen_univ.prod hAo).prod isOpen_Ioo
  let p₀ : (ℝ × EuclideanSpace ℝ (Fin n)) × ℝ := ((f x, e x), 0)
  have hp₀ : p₀ ∈ O := ⟨⟨mem_univ _, hxA⟩, hzeroTime⟩
  have hF : ContDiffOn ℝ ∞ F O := by
    intro q hq
    have hcoord : ContMDiffAt
        (𝓘(ℝ, (ℝ × EuclideanSpace ℝ (Fin n)) × ℝ)) (𝓡 n) ∞
        (fun q => e.symm q.1.2) q :=
      (he q.1.2 hq.1.2.1).comp q
        ((contDiffAt_snd.comp q contDiffAt_fst).contMDiffAt)
    have hpair : ContMDiffAt
        (𝓘(ℝ, (ℝ × EuclideanSpace ℝ (Fin n)) × ℝ))
        (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞ (fun q => (q.2, e.symm q.1.2)) q :=
      contDiffAt_snd.contMDiffAt.prodMk hcoord
    have hflow := (hΦ.contMDiffAt ((isOpen_Ioo.prod hWo).mem_nhds
      (show (q.2, e.symm q.1.2) ∈ Ioo (-δ) δ ×ˢ W from ⟨hq.2, hq.1.2.2⟩))).comp q hpair
    have hfun := (hf.contMDiffAt (hU.mem_nhds
      ((horbit _ hq.1.2.2).1 _ hq.2))).comp q hflow
    exact (hfun.sub ((contDiffAt_fst.comp q contDiffAt_fst).contMDiffAt)).contDiffAt.contDiffWithinAt
  have hFp₀ : F p₀ = 0 := by
    simp only [F, p₀, e.left_inv (mem_extChartAt_source x), hzero x hxW, sub_self]
  let v := mvfderiv (𝓡 n) f x (D.normalizedGradient h x)
  have hv : v < 0 := lt_of_le_of_lt (hcross x hx) (by linarith)
  have hpart : HasDerivAt (fun s => F (p₀.1, s)) v 0 := by
    have hd := (hder x hxW 0 hzeroTime).sub_const (f x)
    rw [hzero x hxW] at hd
    simpa only [F, p₀, e.left_inv (mem_extChartAt_source x), v] using hd
  have hpartial : (fderiv ℝ F p₀).comp
      (ContinuousLinearMap.inr ℝ (ℝ × EuclideanSpace ℝ (Fin n)) ℝ) =
      v • (ContinuousLinearMap.id ℝ ℝ) := by
    have hd := ((hF.contDiffAt (hOo.mem_nhds hp₀)).differentiableAt (by simp)).hasFDerivAt
    have hcomp := hd.comp (0 : ℝ) ((hasFDerivAt_const p₀.1 (0 : ℝ)).prodMk (hasFDerivAt_id (0 : ℝ)))
    have heq := hcomp.unique hpart.hasFDerivAt
    apply ContinuousLinearMap.ext
    intro z
    have hz := congrArg (fun L : ℝ →L[ℝ] ℝ => L z) heq
    change fderiv ℝ F p₀ (0, z) = z * v at hz
    change fderiv ℝ F p₀ (0, z) = v * z
    simpa only [mul_comm] using hz
  have hinv : ((fderiv ℝ F p₀).comp
      (ContinuousLinearMap.inr ℝ (ℝ × EuclideanSpace ℝ (Fin n)) ℝ)).IsInvertible := by
    rw [hpartial]
    refine ⟨(LinearEquiv.smulOfNeZero ℝ ℝ v hv.ne).toContinuousLinearEquiv, ?_⟩
    apply ContinuousLinearMap.ext
    intro z
    rfl
  obtain ⟨B, ψ, hBo, hpB, hψ, hψ₀, hψeq⟩ :=
    exists_smooth_scalar_implicit_function hOo hF hp₀ hinv

  obtain ⟨J, hJ, C, hC, hJC⟩ := mem_nhds_prod_iff.mp (hBo.mem_nhds hpB)
  obtain ⟨ε, hε, hεJ⟩ := Metric.mem_nhds_iff.mp hJ
  obtain ⟨C', hC'C, hC'o, hxC'⟩ := mem_nhds_iff.mp hC
  let V := W ∩ (e.source ∩ e ⁻¹' C')
  have hchart : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := by
    simpa only [e, extChartAt_source] using
      (contMDiffOn_extChartAt (I := 𝓡 n) (x := x) (n := ∞))
  have hVo : IsOpen V := hWo.inter
    (hchart.continuousOn.isOpen_inter_preimage (isOpen_extChartAt_source x) hC'o)
  have hxV : x ∈ V := ⟨hxW, mem_extChartAt_source x, hxC'⟩
  have hVW : V ⊆ W := fun _ hy => hy.1
  have hparam (t : ℝ) (ht : t ∈ Ioo (f x - ε) (f x + ε)) (y : M) (hy : y ∈ V) :
      (t, e y) ∈ B := by
    apply hJC
    refine ⟨hεJ ?_, hC'C hy.2.2⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  let σ : ℝ × M → ℝ := fun q => ψ (q.1, e q.2)
  have hσ : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ σ
      (Ioo (f x - ε) (f x + ε) ×ˢ V) := by
    intro q hq
    have heq := hchart.contMDiffAt (extChartAt_source_mem_nhds' hq.2.2.1)
    have hpair : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n))
        (𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n))) ∞ (fun q : ℝ × M => (q.1, e q.2)) q := by
      rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact contMDiffAt_fst.prodMk (heq.comp q contMDiffAt_snd)
    exact (((hψ.contDiffAt (hBo.mem_nhds (hparam q.1 hq.1 q.2 hq.2))).contMDiffAt).comp
      q hpair).contMDiffWithinAt
  have hhit (t : ℝ) (ht : t ∈ Ioo (f x - ε) (f x + ε)) (y : M) (hy : y ∈ V) :
      σ (t, y) ∈ Ioo (-δ) δ ∧ f (Φ (σ (t, y), y)) = t := by
    obtain ⟨hdom, hval⟩ := hψeq (t, e y) (hparam t ht y hy)
    refine ⟨hdom.2, ?_⟩
    rw [hFp₀] at hval
    change f (Φ (ψ (t, e y), e.symm (e y))) - t = 0 at hval
    rw [e.left_inv hy.2.1] at hval
    exact sub_eq_zero.mp hval
  have hR : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
      (fun q : ℝ × M => Φ (σ q, q.2)) (Ioo (f x - ε) (f x + ε) ×ˢ V) :=
    hΦ.comp (hσ.prodMk contMDiffOn_snd)
      (fun q hq => ⟨(hhit q.1 hq.1 q.2 hq.2).1, hVW hq.2⟩)
  refine ⟨V, ε, δ, Φ, σ, hVo, hxV, hVW.trans hWU, hε, hδ,
    hΦ.mono (prod_mono_right hVW), fun y hy => hzero y (hVW hy),
    fun y hy => horbit y (hVW hy), hσ, hR, ?_, fun y hy => hexp y (hVW hy)⟩
  intro t ht y hy
  obtain ⟨htime, heq⟩ := hhit t ht y hy
  have hcontrol := hitting_time_control hδ hc htime (hder y (hVW hy))
    (fun s hs => hcross _ ((horbit y (hVW hy)).1 s hs))
  rw [hzero y (hVW hy), heq] at hcontrol
  refine ⟨htime, heq, hcontrol.1, hcontrol.2, ?_⟩
  intro hyt
  have hz : σ (t, y) = 0 := by
    apply abs_eq_zero.mp
    apply le_antisymm _ (abs_nonneg _)
    simpa only [hyt, sub_self, abs_zero, zero_div] using hcontrol.1
  rw [hz, hzero y (hVW hy)]
