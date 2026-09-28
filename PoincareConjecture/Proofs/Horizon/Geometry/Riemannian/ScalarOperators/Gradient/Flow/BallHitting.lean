import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Flow.HittingTime
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Flow.CompactBand
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Flow.HittingDifferential

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Manifold ContDiff Bundle Topology InnerProductSpace

namespace PoincareConjecture.LeviCivitaData
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

theorem PoincareConjecture.LeviCivitaData.exists_uniform_level_retraction_on_closedBall
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : PoincareConjecture.RiemannianMetric n M} (D : PoincareConjecture.LeviCivitaData g)
    {f h : M → ℝ} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    (hh : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ h U)
    {l H c : ℝ} (hl : 0 < l) (hH : 0 ≤ H) (hc : 0 < c)
    (hgrad : ∀ y ∈ U, l ≤ g.tangentNorm y (D.gradient h y))
    (hhunit : ∀ y ∈ U, g.tangentNorm y (D.gradient h y) ≤ 1)
    (hfunit : ∀ y ∈ U, g.tangentNorm y (D.gradient f y) ≤ 1)
    (hhess : ∀ y ∈ U, ∀ v : TangentSpace (𝓡 n) y,
      mvfderiv (𝓡 n) h y v = 0 → D.hessian h y v v ≤ H * g.inner y v v)
    (hpair : ∀ y ∈ U, g.inner y (D.gradient f y) (D.gradient h y) ≤ -c)
    (hcomplete : PoincareConjecture.MetricComplete g) (p : M)
    {r R T : ℝ} (hr : 0 ≤ r) (hT : 0 ≤ T) (hroom : r + T / l ≤ R)
    (hball : {y | g.edist p y ≤ ENNReal.ofReal R} ⊆ U) (t : ℝ) :
    let K := {y | g.edist p y ≤ ENNReal.ofReal r ∧ t ≤ f y ∧ f y ≤ t + c * T}
    ∃ (V : Set M) (δ : ℝ) (Φ : ℝ × M → M) (σ : M → ℝ),
      IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ 0 < δ ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ Φ
        (Ioo (-δ) (T + δ) ×ˢ V) ∧
      (∀ y ∈ V, Φ (0, y) = y) ∧
      (∀ y ∈ V, (∀ s ∈ Ioo (-δ) (T + δ), Φ (s, y) ∈ U) ∧
        IsMIntegralCurveOn (I := 𝓡 n) (fun s => Φ (s, y))
          (D.normalizedGradient h) (Ioo (-δ) (T + δ))) ∧
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ σ V ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ (fun y => Φ (σ y, y)) V ∧
      (∀ y ∈ V, σ y ∈ Ioo (-δ) (T + δ) ∧ f (Φ (σ y, y)) = t ∧
        |σ y| ≤ |f y - t| / c ∧ (0 ≤ σ y ↔ t ≤ f y) ∧
        (f y = t → Φ (σ y, y) = y)) ∧
      ∀ y ∈ K, σ y ∈ Icc 0 T ∧
        ∀ v : TangentSpace (𝓡 n) y,
          g.tangentNorm (Φ (σ y, y))
              (mfderiv (𝓡 n) (𝓡 n) (fun z => Φ (σ z, z)) y v) ≤
            (1 + 1 / c) * Real.exp ((H / l ^ 2) * ((f y - t) / c)) *
              g.tangentNorm y v := by

  dsimp only
  let K := {y | g.edist p y ≤ ENNReal.ofReal r ∧ t ≤ f y ∧ f y ≤ t+c*T}
  have hcross (y : M) (hy : y ∈ U) :
      mvfderiv (𝓡 n) f y (D.normalizedGradient h y) ≤ -c :=
    normalizedGradient_cross_le_of_pairing D f h y hl hc (hgrad y hy) (hhunit y hy) (hpair y hy)
  obtain ⟨W, δ, Φ, hWo, hBW, hWU, hδ, hΦ, hzero, horbit, hexp⟩ :=
    D.exists_uniform_normalizedGradient_manifoldFlow_on_closedBall
      hU hh hl hH hgrad hhess hcomplete p hr hT hroom hball
  let F : ℝ × M → ℝ := fun q => f (Φ q)
  let F' : ℝ × M → ℝ := fun q => mvfderiv (𝓡 n) f (Φ q) (D.normalizedGradient h (Φ q))
  have hFsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F
      (Ioo (-δ) (T+δ) ×ˢ W) :=
    hf.comp hΦ (fun q hq => (horbit q.2 hq.2).1 q.1 hq.1)
  have hder (y : M) (hy : y∈W) (s : ℝ) (hs : s∈Ioo (-δ) (T+δ)) :
      HasDerivAt (fun u => F (u,y)) (F' (s,y)) s :=
    scalar_derivative_along_curve
      ((hf.contMDiffAt (hU.mem_nhds ((horbit y hy).1 s hs))).mdifferentiableAt (by simp))
      ((horbit y hy).2.isMIntegralCurveAt (isOpen_Ioo.mem_nhds hs))
  have hbound (y : M) (hy : y∈W) (s : ℝ) (hs : s∈Ioo (-δ) (T+δ)) :
      F' (s,y) ≤ -c := hcross _ ((horbit y hy).1 s hs)
  obtain ⟨V, σ, hVo, hVW, hKV, hσ, hhit, htimes⟩ :=
    Poincare.Manifold.exists_smooth_hitting_time_of_derivative_le_neg
      hWo hT hδ hc hFsmooth hder hbound t
  have hK : K ⊆ V := by
    intro y hy
    apply hKV
    have hyW := hBW hy.1
    refine ⟨hyW, ?_, ?_⟩
    · simpa only [F, hzero y hyW] using hy.2.1
    · simpa only [F, hzero y hyW] using hy.2.2
  have hR : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (fun y => Φ (σ y,y)) V :=
    hΦ.comp (hσ.prodMk contMDiffOn_id) (fun y hy => ⟨(hhit y hy).1,hVW hy⟩)
  refine ⟨V, δ, Φ, σ, hVo, hK, hVW.trans hWU, hδ,
    hΦ.mono (prod_mono_right hVW), fun y hy => hzero y (hVW hy),
    fun y hy => horbit y (hVW hy), hσ, hR, ?_, ?_⟩
  · intro y hy
    refine ⟨(hhit y hy).1, (hhit y hy).2.1, ?_, ?_, ?_⟩
    · simpa only [F, hzero y (hVW hy)] using (hhit y hy).2.2.1
    · simpa only [F, hzero y (hVW hy)] using (hhit y hy).2.2.2.1
    · intro hfy
      have heq : F (0,y)=t := by simpa only [F,hzero y (hVW hy)] using hfy
      rw [(hhit y hy).2.2.2.2 heq,hzero y (hVW hy)]
  intro y hy
  have hyV := hK hy
  have hyW := hVW hyV
  have htime : σ y ∈ Icc 0 T := htimes y hyV
    (by simpa only [F,hzero y hyW] using hy.2.1)
    (by simpa only [F,hzero y hyW] using hy.2.2)
  refine ⟨htime, ?_⟩
  intro v
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hi (z : M) (u w : TangentSpace (𝓡 n) z) : ⟪u,w⟫_ℝ=g.inner z u w := rfl
  let z := Φ (σ y,y)
  have hzU : z∈U := (horbit y hyW).1 _ (hhit y hyV).1
  have hsigmad := (hσ.contMDiffAt (hVo.mem_nhds hyV)).mdifferentiableAt (by simp)
  have hfd := (hf.contMDiffAt (hU.mem_nhds hzU)).mdifferentiableAt (by simp)
  have hlevel : (fun q => f (Φ (σ q,q))) =ᶠ[𝓝 y] (fun _ => t) := by
    filter_upwards [hVo.mem_nhds hyV] with q hq
    exact (hhit q hq).2.1
  have hL : ∀ w : TangentSpace (𝓡 n) y, mvfderiv (𝓡 n) h y w=0 →
      g.tangentNorm z (mfderiv (𝓡 n) (𝓡 n) (fun q => Φ (σ y,q)) y w) ≤
        Real.exp ((H/l^2)*σ y)*g.tangentNorm y w := by
    intro w hw
    have he := (hexp y hyW (σ y) htime).2 w hw
    rw [← hi,← hi,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at he
    have heq : (Real.exp ((H/l^2)*σ y))^2 = Real.exp (2*(H/l^2)*σ y) := by
      rw [pow_two,←Real.exp_add]
      congr 1
      ring
    change ‖mfderiv (𝓡 n) (𝓡 n) (fun q => Φ (σ y,q)) y w‖ ≤ Real.exp ((H/l^2)*σ y)*‖w‖
    have hpos := mul_nonneg (Real.exp_pos ((H/l^2)*σ y)).le (norm_nonneg w)
    nlinarith [norm_nonneg (mfderiv (𝓡 n) (𝓡 n) (fun q => Φ (σ y,q)) y w)]
  have hd := D.tangentNorm_mfderiv_hittingMap_le_of_expansion
    hU hWo hh hl hgrad (by linarith : -δ<0) (by linarith : 0<T+δ)
    hΦ hzero horbit hyW (hhit y hyV).1 hsigmad hfd hlevel hc
    (Real.exp_pos _).le (hhunit z hzU) (hfunit z hzU) (hpair z hzU) hL v
  apply hd.trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0≤1+1/c)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hH (sq_nonneg l))
  have htimebound := (hhit y hyV).2.2.1
  simpa only [F,hzero y hyW,abs_of_nonneg htime.1,abs_of_nonneg (sub_nonneg.mpr hy.2.1)]
    using htimebound
