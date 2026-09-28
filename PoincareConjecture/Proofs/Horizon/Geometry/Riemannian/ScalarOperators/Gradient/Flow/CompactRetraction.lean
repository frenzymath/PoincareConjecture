import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Flow.CompactBand
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Flow.HittingTime
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Flow.HittingDifferential
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Flow.LevelEvolution
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Flow.Transport
import PoincareConjecture.Proofs.Horizon.Analysis.InnerProductSpace.ObliqueProjection







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Function TopologicalSpace
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


theorem exists_positive_level_retraction_on_compact_buffer
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : PoincareConjecture.RiemannianMetric n M} (D : PoincareConjecture.LeviCivitaData g)
    {f : M → ℝ} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    {l H : ℝ} (hl : 0 < l) (hH : 0 ≤ H)
    (hgrad : ∀ y ∈ U, l ≤ g.tangentNorm y (D.gradient f y))
    (hhess : ∀ y ∈ U, ∀ v : TangentSpace (𝓡 n) y,
      mvfderiv (𝓡 n) f y v = 0 → D.hessian f y v v ≤ H * g.inner y v v)
    {K S : Set M} (hK : IsCompact K) (hS : IsCompact S)
    (hKS : K ⊆ S) (hSU : S ⊆ U) {T : ℝ} (hT : 0 ≤ T)
    (hbuffer : ∀ x ∈ K, ∀ y, g.edist x y ≤ ENNReal.ofReal (T / l) → y ∈ S)
    (t : ℝ) :
    ∃ (V : Set M) (Q : M → M),
      IsOpen V ∧ {y | y ∈ K ∧ f y ∈ Icc (t - T) t} ⊆ V ∧
      V ⊆ U ∧ ContMDiffOn (𝓡 n) (𝓡 n) ∞ Q V ∧
      (∀ y ∈ V, Q y ∈ U ∧ f (Q y) = t ∧ (f y = t → Q y = y)) ∧
      ∀ y : M, y ∈ K → f y ∈ Icc (t - T) t →
        g.edist y (Q y) ≤ ENNReal.ofReal ((t - f y) / l) ∧
        ∀ v : TangentSpace (𝓡 n) y,
          g.tangentNorm (Q y) (mfderiv (𝓡 n) (𝓡 n) Q y v) ≤
            Real.exp ((H / l ^ 2) * (t - f y)) * g.tangentNorm y v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hi (z : M) (v w : TangentSpace (𝓡 n) z) : ⟪v,w⟫_ℝ = g.inner z v w := rfl
  have hqpos (y : M) (hy : y ∈ U) :
      0 < g.inner y (D.gradient f y) (D.gradient f y) := by
    rw [← hi, real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (hl.trans_le (hgrad y hy))
  obtain ⟨W, δ, Φ, hWo, hKW, hWU, hδ, hΦ, hzero, horbit, hexp⟩ :=
    D.exists_uniform_normalizedGradient_manifoldFlow_on_compact_buffer
      hU hf hl hH hgrad hhess hK hS hKS hSU hT hbuffer
  let σ : M → ℝ := fun y => t - f y
  let V : Set M := W ∩ σ ⁻¹' Ioo (-δ) (T + δ)
  let Q : M → M := fun y => Φ (σ y, y)
  have hVo : IsOpen V :=
    (continuousOn_const.sub (hf.continuousOn.mono hWU)).isOpen_inter_preimage hWo isOpen_Ioo
  have hKV : {y | y ∈ K ∧ f y ∈ Icc (t - T) t} ⊆ V := by
    rintro y ⟨hy, hfy⟩
    exact ⟨hKW hy, ⟨by dsimp only [σ]; linarith [hfy.2],
      by dsimp only [σ]; linarith [hfy.1]⟩⟩
  have hσd (y : M) (hy : y ∈ W) : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ σ y :=
    contMDiffAt_const.sub (hf.contMDiffAt (hU.mem_nhds (hWU hy)))
  have hΦd (y : M) (hy : y ∈ V) :
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ Φ (σ y,y) :=
    hΦ.contMDiffAt ((isOpen_Ioo.prod hWo).mem_nhds ⟨hy.2,hy.1⟩)
  have hQd : ContMDiffOn (𝓡 n) (𝓡 n) ∞ Q V := by
    intro y hy
    exact ((hΦd y hy).comp (f := fun z => (σ z,z)) y
      ((hσd y hy.1).prodMk contMDiffAt_id)).contMDiffWithinAt
  refine ⟨V, Q, hVo, hKV, (fun _ hy => hWU hy.1), hQd, ?_, ?_⟩
  · intro y hy
    refine ⟨(horbit y hy.1).1 _ hy.2, ?_, ?_⟩
    · have he := D.comp_normalizedGradient_eq_add_on isOpen_Ioo isPreconnected_Ioo
        (fun s hs => (hf.contMDiffAt (hU.mem_nhds ((horbit y hy.1).1 s hs))).mdifferentiableAt (by simp))
        (fun s hs => (hqpos _ ((horbit y hy.1).1 s hs)).ne')
        (horbit y hy.1).2 (show 0 ∈ Ioo (-δ) (T + δ) from ⟨by linarith,by linarith⟩) hy.2
      simpa [Q, σ, hzero y hy.1] using he
    · intro hyt
      change Φ (t-f y,y) = y
      rw [hyt, sub_self, hzero y hy.1]
  intro y hyr hfy
  have hy : y ∈ V := hKV ⟨hyr,hfy⟩
  have hs : σ y ∈ Icc 0 T := ⟨by dsimp only [σ]; linarith [hfy.2],
    by dsimp only [σ]; linarith [hfy.1]⟩
  constructor
  · have hcurve : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞
        (fun s => Φ (s,y)) (Ioo (-δ) (T+δ)) := by
      apply hΦ.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn
      exact fun s hs => ⟨hs,hy.1⟩
    have hd := D.edist_le_of_normalizedGradient_curve isOpen_Ioo hcurve
      (horbit y hy.1).2 hl hs.1
      (fun s hs' => ⟨by linarith [hs'.1], by linarith [hs'.2,hs.2]⟩)
      (fun s hs' => hgrad _ ((horbit y hy.1).1 s hs'))
    simpa only [hzero y hy.1,sub_zero] using hd
  intro v
  let L := mfderiv (𝓡 n) (𝓡 n) (fun z => Φ (σ y,z)) y
  let w := v - (⟪D.gradient f y,v⟫_ℝ / ‖D.gradient f y‖ ^ 2) • D.gradient f y
  have hw : mvfderiv (𝓡 n) f y w = 0 := by
    rw [← D.inner_gradient, ← hi]
    exact Poincare.InnerProductSpace.inner_sub_normal_component _ _
  have hwn : ‖w‖ ≤ ‖v‖ := Poincare.InnerProductSpace.norm_sub_normal_component_le _ _
  have htrans : L (D.normalizedGradient f y) = D.normalizedGradient f (Q y) :=
    Poincare.Manifold.mfderiv_localFlow_vectorField hU hWo
      ((D.contMDiffOn_normalizedGradient_of_lower_bound hU hf hl hgrad).of_le (by simp))
      (by linarith : -δ < 0) (by linarith : 0 < T+δ) (hΦ.of_le (by simp))
      hzero (fun z hz => (horbit z hz).1) (fun z hz => (horbit z hz).2) hy.1 hy.2
  have hpair : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n))
      (fun z => (σ z,z)) y := (hσd y hy.1).mdifferentiableAt (by simp) |>.prodMk mdifferentiableAt_id
  have hchain : mfderiv (𝓡 n) (𝓡 n) Q y v =
      (mvfderiv (𝓡 n) σ y v) • D.normalizedGradient f (Q y) + L v := by
    have he := congrArg (fun A => A v) (mfderiv_comp (f := fun z => (σ z,z)) y
      ((hΦd y hy).mdifferentiableAt (by simp)) hpair)
    erw [mfderiv_prodMk ((hσd y hy.1).mdifferentiableAt (by simp)) mdifferentiableAt_id,
      mfderiv_id] at he
    change mfderiv (𝓡 n) (𝓡 n) Q y v =
      mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) Φ (σ y,y)
        (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) σ y v,v) at he
    rw [mfderiv_prod_eq_add_apply ((hΦd y hy).mdifferentiableAt (by simp)),
      ((horbit y hy.1).2.isMIntegralCurveAt (isOpen_Ioo.mem_nhds hy.2)).hasMFDerivAt.mfderiv] at he
    change mfderiv (𝓡 n) (𝓡 n) Q y v =
      (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) σ y v) • D.normalizedGradient f (Q y) + L v at he
    simpa [mvfderiv, NormedSpace.fromTangentSpace] using he
  have hσv : mvfderiv (𝓡 n) σ y v = -mvfderiv (𝓡 n) f y v := by
    dsimp only [σ]
    rw [mvfderiv_fun_sub mdifferentiableAt_const
      ((hf.contMDiffAt (hU.mem_nhds (hWU hy.1))).mdifferentiableAt (by simp))]
    simp only [mvfderiv_const, zero_sub, neg_apply]
  have hw' : w = v - (mvfderiv (𝓡 n) f y v) • D.normalizedGradient f y := by
    dsimp only [w, PoincareConjecture.LeviCivitaData.normalizedGradient]
    rw [← D.inner_gradient, ← hi, ← hi, real_inner_self_eq_norm_sq, smul_smul, div_eq_mul_inv]
  have hderiv : mfderiv (𝓡 n) (𝓡 n) Q y v = L w := by
    rw [hchain, hσv, hw', map_sub, map_smul, htrans, neg_smul]
    module
  rw [hderiv]
  have hsq := (hexp y hy.1 (σ y) hs).2.2 w hw
  change g.inner (Q y) (L w) (L w) ≤ g.inner y w w * Real.exp (2*(H/l^2)*σ y) at hsq
  rw [← hi, ← hi, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hsq
  have he : (Real.exp ((H/l^2)*σ y))^2 = Real.exp (2*(H/l^2)*σ y) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hnonneg : 0 ≤ Real.exp ((H/l^2)*σ y) * ‖w‖ :=
    mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  have hnorm : ‖L w‖ ≤ Real.exp ((H/l^2)*σ y) * ‖w‖ := by
    nlinarith [norm_nonneg (L w)]
  exact hnorm.trans (mul_le_mul_of_nonneg_left hwn (Real.exp_pos _).le)


theorem exists_opposite_level_retraction_on_compact_buffer
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
    {A S : Set M} (hA : IsCompact A) (hS : IsCompact S)
    (hAS : A ⊆ S) (hSU : S ⊆ U) {T : ℝ} (hT : 0 ≤ T)
    (hbuffer : ∀ x ∈ A, ∀ y, g.edist x y ≤ ENNReal.ofReal (T / l) → y ∈ S)
    (t : ℝ) :
    let K := {y | y ∈ A ∧ t ≤ f y ∧ f y ≤ t + c * T}
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
        g.edist y (Φ (σ y, y)) ≤ ENNReal.ofReal ((f y - t) / (c * l)) ∧
        ∀ v : TangentSpace (𝓡 n) y,
          g.tangentNorm (Φ (σ y, y))
              (mfderiv (𝓡 n) (𝓡 n) (fun z => Φ (σ z, z)) y v) ≤
            (1 + 1 / c) * Real.exp ((H / l ^ 2) * ((f y - t) / c)) *
              g.tangentNorm y v := by

  dsimp only
  let K := {y | y ∈ A ∧ t ≤ f y ∧ f y ≤ t+c*T}
  have hcross (y : M) (hy : y ∈ U) :
      mvfderiv (𝓡 n) f y (D.normalizedGradient h y) ≤ -c :=
    normalizedGradient_cross_le_of_pairing D f h y hl hc (hgrad y hy) (hhunit y hy) (hpair y hy)
  obtain ⟨W, δ, Φ, hWo, hBW, hWU, hδ, hΦ, hzero, horbit, hexp⟩ :=
    D.exists_uniform_normalizedGradient_manifoldFlow_on_compact_buffer
      hU hh hl hH hgrad hhess hA hS hAS hSU hT hbuffer
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
  refine ⟨htime, ?_, ?_⟩
  · refine ((hexp y hyW (σ y) htime).2.1).trans (ENNReal.ofReal_le_ofReal ?_)
    have htimebound := (hhit y hyV).2.2.1
    have hsig : σ y ≤ (f y - t) / c := by
      simpa only [F, hzero y hyW, abs_of_nonneg htime.1,
        abs_of_nonneg (sub_nonneg.mpr hy.2.1)] using htimebound
    simpa only [div_div] using div_le_div_of_nonneg_right hsig hl.le
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
    have he := (hexp y hyW (σ y) htime).2.2 w hw
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



end PoincareConjecture.LeviCivitaData
