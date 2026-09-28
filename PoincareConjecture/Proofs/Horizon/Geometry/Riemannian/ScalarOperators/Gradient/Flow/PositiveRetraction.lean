import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Flow.CompactBand
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Flow.LevelEvolution
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Flow.NormalizedField
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Flow.Transport
import PoincareConjecture.Proofs.Horizon.Analysis.InnerProductSpace.ObliqueProjection

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Manifold ContDiff Bundle Topology InnerProductSpace

theorem PoincareConjecture.LeviCivitaData.exists_positive_level_retraction_on_closedBall
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : PoincareConjecture.RiemannianMetric n M} (D : PoincareConjecture.LeviCivitaData g)
    {f : M → ℝ} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    {l H : ℝ} (hl : 0 < l) (hH : 0 ≤ H)
    (hgrad : ∀ y ∈ U, l ≤ g.tangentNorm y (D.gradient f y))
    (hhess : ∀ y ∈ U, ∀ v : TangentSpace (𝓡 n) y,
      mvfderiv (𝓡 n) f y v = 0 → D.hessian f y v v ≤ H * g.inner y v v)
    (hcomplete : PoincareConjecture.MetricComplete g) (p : M)
    {r R T : ℝ} (hr : 0 ≤ r) (hT : 0 ≤ T) (hroom : r + T / l ≤ R)
    (hball : {y | g.edist p y ≤ ENNReal.ofReal R} ⊆ U) (t : ℝ) :
    ∃ (V : Set M) (Q : M → M),
      IsOpen V ∧ {y | g.edist p y ≤ ENNReal.ofReal r ∧ f y ∈ Icc (t - T) t} ⊆ V ∧
      V ⊆ U ∧ ContMDiffOn (𝓡 n) (𝓡 n) ∞ Q V ∧
      (∀ y ∈ V, Q y ∈ U ∧ f (Q y) = t ∧ (f y = t → Q y = y)) ∧
      ∀ y : M, g.edist p y ≤ ENNReal.ofReal r → f y ∈ Icc (t - T) t →
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
    D.exists_uniform_normalizedGradient_manifoldFlow_on_closedBall
      hU hf hl hH hgrad hhess hcomplete p hr hT hroom hball
  let σ : M → ℝ := fun y => t - f y
  let V : Set M := W ∩ σ ⁻¹' Ioo (-δ) (T + δ)
  let Q : M → M := fun y => Φ (σ y, y)
  have hVo : IsOpen V :=
    (continuousOn_const.sub (hf.continuousOn.mono hWU)).isOpen_inter_preimage hWo isOpen_Ioo
  have hKV : {y | g.edist p y ≤ ENNReal.ofReal r ∧ f y ∈ Icc (t - T) t} ⊆ V := by
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
  have hsq := (hexp y hy.1 (σ y) hs).2 w hw
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
