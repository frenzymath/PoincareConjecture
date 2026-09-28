import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularFiberFlow
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.CompactSet
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.CompactImage







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Function TopologicalSpace MeasureTheory
open Poincare.Geometry.Manifold.RegularFiber
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology


private theorem curve_eqOn_Ioo
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {X : (x : M) → TangentSpace (𝓡 n) x} {U : Set M} (hU : IsOpen U)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) 1 (T% X) U)
    {α β : ℝ → M} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hαU : ∀ t ∈ Ioo a b, α t ∈ U)
    (hα : IsMIntegralCurveOn (I := 𝓡 n) α X (Ioo a b))
    (hβ : IsMIntegralCurveOn (I := 𝓡 n) β X (Ioo a b))
    (hinit : α t₀ = β t₀) : EqOn α β (Ioo a b) := by
  let S := {t | α t = β t} ∩ Ioo a b
  suffices hsub : Ioo a b ⊆ S from fun t ht => (hsub ht).1
  apply isPreconnected_Ioo.subset_of_closure_inter_subset (s := Ioo a b) (u := S) _
    ⟨t₀, ⟨ht₀, ⟨hinit, ht₀⟩⟩⟩
  · dsimp only [S]
    rw [inter_comm, ← Subtype.image_preimage_val, inter_comm, ← Subtype.image_preimage_val,
      image_subset_image_iff Subtype.val_injective, preimage_ofPred_eq]
    intro t ht
    rw [mem_preimage, ← closure_subtype] at ht
    revert ht t
    apply IsClosed.closure_subset (isClosed_eq _ _)
    · rw [continuous_iff_continuousAt]
      rintro ⟨t, ht⟩
      apply ContinuousAt.comp _ continuousAt_subtype_val
      exact (hα.continuousWithinAt ht).continuousAt (Ioo_mem_nhds ht.1 ht.2)
    · rw [continuous_iff_continuousAt]
      rintro ⟨t, ht⟩
      apply ContinuousAt.comp _ continuousAt_subtype_val
      exact (hβ.continuousWithinAt ht).continuousAt (Ioo_mem_nhds ht.1 ht.2)
  · rw [isOpen_iff_mem_nhds]
    intro t ht
    have hmem := Ioo_mem_nhds ht.2.1 ht.2.2
    have heq := isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless
      (hX.contMDiffAt (hU.mem_nhds (hαU t ht.2)))
      (hα.isMIntegralCurveAt hmem) (hβ.isMIntegralCurveAt hmem) ht.1
    exact (heq.and hmem).mono (fun _ hs => hs)



private theorem normalizedGradient_smooth_of_regular
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : PoincareConjecture.RiemannianMetric n M} (D : PoincareConjecture.LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x ≠ 0) :
    ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% (D.normalizedGradient f)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro x
  have hgn : D.gradient f x ≠ 0 := by
    exact fun hz => hreg x ((g.gradient_eq_zero_iff_mfderiv_eq_zero f x).mp hz)
  have hp : g.inner x (D.gradient f x) (D.gradient f x) ≠ 0 :=
    ne_of_gt (g.pos x _ hgn)
  have hgrad := D.contMDiffAt_gradient (hf.contMDiffAt (x := x))
  have hpair : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => g.inner y (D.gradient f y) (D.gradient f y)) x :=
    hgrad.inner_bundle hgrad
  exact ((contDiffAt_inv ℝ hp).contMDiffAt.comp x hpair).smul_section hgrad


private theorem scalar_le_of_integrable_slice_bound
    {A : ℝ → ℝ} (hAi : Integrable A) (hA : ∀ s, 0 ≤ A s)
    {B C V t T : ℝ} (hC : 0 ≤ C) (hT : 0 < T)
    (hbound : ∀ s ∈ Icc (t - T) t, B ≤ C * A s)
    (hvolume : (∫ s, A s) ≤ V) : B ≤ C / T * V := by
  have hI : volume.real (Icc (t - T) t) = T := by
    simpa using hT.le
  have hBi : IntegrableOn (fun _ : ℝ => B) (Icc (t - T) t) :=
    integrableOn_const (hs := isCompact_Icc.measure_ne_top)
  have hCB : B * T ≤ C * ∫ s in Icc (t - T) t, A s := by
    calc
      _ = ∫ s in Icc (t - T) t, B := by simp [hI, mul_comm]
      _ ≤ ∫ s in Icc (t - T) t, C * A s :=
        integral_mono_ae hBi (hAi.integrableOn.const_mul C)
          (ae_restrict_of_forall_mem isClosed_Icc.measurableSet hbound)
      _ = _ := integral_const_mul C _
  have hsub : (∫ s in Icc (t - T) t, A s) ≤ V :=
    (setIntegral_le_integral hAi (Eventually.of_forall hA)).trans hvolume
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hT).mpr
  have hmul := mul_le_mul_of_nonneg_left hsub hC
  exact hCB.trans hmul


private theorem tangentNorm_le_of_inner_exp_bound
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (g : PoincareConjecture.RiemannianMetric n M) {x y : M}
    (v : TangentSpace (𝓡 n) x) (w : TangentSpace (𝓡 n) y) (a : ℝ)
    (h : g.inner y w w ≤ g.inner x v v * Real.exp (2 * a)) :
    g.tangentNorm y w ≤ Real.exp a * g.tangentNorm x v := by
  change Real.sqrt (g.inner y w w) ≤ Real.exp a * Real.sqrt (g.inner x v v)
  calc
    _ ≤ Real.sqrt (g.inner x v v * Real.exp (2 * a)) := Real.sqrt_le_sqrt h
    _ = _ := by
      have hn : 0 ≤ g.inner x v v := by
        by_cases hv : v = 0
        · simp [hv]
        · exact (g.pos x v hv).le
      rw [Real.sqrt_mul hn, two_mul, Real.exp_add,
        Real.sqrt_mul_self (Real.exp_pos a).le, mul_comm]


private theorem regularLevel_mass_le_of_smooth_image
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) ∞ M]
    (g : PoincareConjecture.RiemannianMetric (n + 1) M)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x ∈ (⊤ : Opens M), mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)
    {Q : M → M} {V K J : Set M} (hV : IsOpen V) (hK : IsCompact K)
    (hJ : IsCompact J) (hKV : K ⊆ V)
    (hQ : ContMDiffOn (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ Q V)
    {a b C : ℝ} (hC : 0 < C)
    (hlevel : ∀ x ∈ V, f x = a → f (Q x) = b)
    (hcover : ∀ x ∈ J, f x = b → ∃ y ∈ K, f y = a ∧ Q y = x)
    (hbound : ∀ x ∈ V, f x = a → ∀ v : TangentSpace (𝓡 (n + 1)) x,
      mvfderiv (𝓡 (n + 1)) f x v = 0 →
        g.tangentNorm (Q x) (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) Q x v) ≤
          C * g.tangentNorm x v) :
    (g.regularLevelVolume hf ⊤ hreg b).real {z | openLevelIncl f ⊤ b z ∈ J} ≤
      C ^ n * (g.regularLevelVolume hf ⊤ hreg a).real
        {z | openLevelIncl f ⊤ a z ∈ K} := by
  classical
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openLevelSetChartedSpace hf ⊤ hreg n a
  let := isManifold_openLevelSet hf ⊤ hreg n a
  let := openLevelSetChartedSpace hf ⊤ hreg n b
  let := isManifold_openLevelSet hf ⊤ hreg n b
  let incA := openLevelIncl f ⊤ a
  let incB := openLevelIncl f ⊤ b
  let s : Set (openLevelSet f ⊤ a) := incA ⁻¹' K
  let j : Set (openLevelSet f ⊤ b) := incB ⁻¹' J
  have hcompact (c : ℝ) {E : Set M} (hE : IsCompact E) :
      IsCompact (openLevelIncl f ⊤ c ⁻¹' E) := by
    apply (isEmbedding_openLevelIncl f ⊤ c).isCompact_iff.mpr
    rw [image_preimage_eq_inter_range, range_openLevelIncl]
    simpa using hE.inter_right (isClosed_singleton.preimage hf.continuous)
  have hs : IsCompact s := hcompact a hK
  have hj : IsCompact j := hcompact b hJ
  rcases j.eq_empty_or_nonempty with hj0 | hjne
  · change (g.regularLevelVolume hf ⊤ hreg b).real j ≤ _
    rw [hj0]
    simp only [measureReal_empty]
    exact mul_nonneg (pow_nonneg hC.le _) ENNReal.toReal_nonneg
  obtain ⟨z0, hz0⟩ := hjne
  let W : Set (openLevelSet f ⊤ a) := incA ⁻¹' V
  have hW : IsOpen W := hV.preimage (isEmbedding_openLevelIncl f ⊤ a).continuous
  have hsW : s ⊆ W := fun x hx => hKV hx
  let F : openLevelSet f ⊤ a → openLevelSet f ⊤ b := fun x =>
    if hx : x ∈ W then ⟨⟨Q (incA x), mem_univ _⟩, hlevel _ hx x.2⟩ else z0
  have heq : EqOn (incB ∘ F) (Q ∘ incA) W := by
    intro x hx
    simp only [F, dif_pos hx, Function.comp_apply, incB, openLevelIncl]
  have hincA : ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ incA :=
    contMDiff_openLevelIncl hf ⊤ hreg n a
  have hFs : ContMDiffOn (𝓡 n) (𝓡 (n + 1)) ∞ (incB ∘ F) W :=
    (hQ.comp hincA.contMDiffOn (fun _ hx => hx)).congr heq
  have hFb : ∀ x ∈ W, ∀ v : TangentSpace (𝓡 n) x,
      g.tangentNorm (incB (F x)) (mfderiv (𝓡 n) (𝓡 (n + 1)) (incB ∘ F) x v) ≤
        C * g.tangentNorm (incA x) (mfderiv (𝓡 n) (𝓡 (n + 1)) incA x v) := by
    intro x hx v
    have hevent : incB ∘ F =ᶠ[𝓝 x] Q ∘ incA :=
      eventually_nhds_iff.mpr ⟨W, heq, hW, hx⟩
    have heqx : incB (F x) = Q (incA x) := heq hx
    rw [heqx, hevent.mfderiv_eq, mfderiv_comp x
      ((hQ.contMDiffAt (hV.mem_nhds hx)).mdifferentiableAt (by simp))
      (hincA.mdifferentiable (by simp) x)]
    apply hbound _ hx x.2
    have hrange := range_mfderiv_openLevelIncl hf ⊤ hreg n a x
    have hm : (mfderiv (𝓡 n) (𝓡 (n + 1)) incA x) v ∈
        (mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f (incA x)).ker := by
      rw [← hrange]
      exact ⟨v, rfl⟩
    exact hm
  have hle := g.regularLevelVolume_image_le_of_ambient_tangentNorm_le_on_compact
    hf ⊤ hreg ⊤ hreg a b F hW hs hsW hC hFs hFb
  have hsub : j ⊆ F '' s := by
    intro z hz
    obtain ⟨y, hyK, hyf, hyQ⟩ := hcover (incB z) hz z.2
    let yL : openLevelSet f ⊤ a := ⟨⟨y, mem_univ _⟩, hyf⟩
    have hyW : yL ∈ W := hKV hyK
    refine ⟨yL, hyK, ?_⟩
    apply (isEmbedding_openLevelIncl f ⊤ b).injective
    exact (heq hyW).trans hyQ
  have hfinite : g.regularLevelVolume hf ⊤ hreg a s ≠ ⊤ :=
    by
      change (g.regularLevelMetric hf ⊤ hreg a).volumeMeasure s ≠ ⊤
      exact hs.measure_ne_top
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hfinite)
    ((measure_mono hsub).trans hle)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hC.le] at hreal
  exact hreal



theorem PoincareConjecture.RiemannianMetric.openFiber_sliceVolume_le_on_ambient_closedBall
    {d k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin ((d + 1) + k))) M]
    [IsManifold (𝓡 ((d + 1) + k)) ∞ M]
    (g : PoincareConjecture.RiemannianMetric ((d + 1) + k) M)
    (hc : PoincareConjecture.MetricComplete g)
    {f : M → Fin k → ℝ} {φ : M → ℝ}
    (hf : ContMDiff (𝓡 ((d + 1) + k)) 𝓘(ℝ, Fin k → ℝ) ∞ f)
    (hφ : ContMDiff (𝓡 ((d + 1) + k)) 𝓘(ℝ, ℝ) ∞ φ)
    (U : TopologicalSpace.Opens M)
    (hreg : ∀ x ∈ U, Function.Surjective
      (mfderiv (𝓡 ((d + 1) + k)) 𝓘(ℝ, Fin k → ℝ) f x))
    (c : Fin k → ℝ) (p : M) {l H r R T : ℝ}
    (hl : 0 < l) (hH : 0 ≤ H) (hr : 0 ≤ r) (hT : 0 < T)
    (hroom : r + 2 * T / l ≤ R)
    (hball : ∀ y, g.edist p y ≤ ENNReal.ofReal R → y ∈ U) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((d + 1) + k))) =
      (d + 1) + k) := ⟨finrank_euclideanSpace_fin⟩
    letI := openFiberChartedSpace (m := d + 1) hf U hreg c
    letI := isManifold_openFiber (m := d + 1) hf U hreg c
    let incl := openFiberIncl f U c
    let gL := g.openRegularFiberMetric hf U hreg c
    let DL := gL.leviCivitaData
    let φL := φ ∘ incl
    let hφL := hφ.comp (contMDiff_openFiberIncl (m := d + 1) hf U hreg c)
    (∀ y : openFiber f U c,
      l ≤ gL.tangentNorm y (DL.gradient φL y) ∧
      gL.tangentNorm y (DL.gradient φL y) ≤ 1) →
    (∀ y : openFiber f U c, ∀ v : TangentSpace (𝓡 (d + 1)) y,
      mvfderiv (𝓡 (d + 1)) φL y v = 0 →
        DL.hessian φL y v v ≤ H * gL.inner y v v) →
    ∃ hregφ : ∀ y ∈ (⊤ : Opens (openFiber f U c)),
        mfderiv (𝓡 (d + 1)) 𝓘(ℝ, ℝ) φL y ≠ 0,
      ∀ t : ℝ,
        (gL.regularLevelVolume hφL ⊤ hregφ t).real
          {z | g.edist p (incl (openLevelIncl φL ⊤ t z)) ≤ ENNReal.ofReal r} ≤
        Real.exp ((d : ℝ) * H * T / l ^ 2) / T *
          gL.volumeMeasure.real
            {y | g.edist p (incl y) ≤ ENNReal.ofReal (r + T / l)} := by
  classical
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((d + 1) + k))) =
      (d + 1) + k) := ⟨finrank_euclideanSpace_fin⟩
  let := openFiberChartedSpace (m := d + 1) hf U hreg c
  let := isManifold_openFiber (m := d + 1) hf U hreg c
  let incl := openFiberIncl f U c
  let gL := g.openRegularFiberMetric hf U hreg c
  let DL := gL.leviCivitaData
  let φL := φ ∘ incl
  let hφL := hφ.comp (contMDiff_openFiberIncl (m := d + 1) hf U hreg c)
  dsimp only
  intro hgrad hhess
  have hregφ : ∀ y ∈ (⊤ : Opens (openFiber f U c)),
      mfderiv (𝓡 (d + 1)) 𝓘(ℝ, ℝ) φL y ≠ 0 := by
    intro y hy hz
    have hgzero := (gL.gradient_eq_zero_iff_mfderiv_eq_zero φL y).mpr hz
    have hn : gL.tangentNorm y (DL.gradient φL y) = 0 := by
      change gL.tangentNorm y (gL.gradient φL y) = 0
      simp only [hgzero, PoincareConjecture.RiemannianMetric.tangentNorm, map_zero, Real.sqrt_zero]
    linarith [(hgrad y).1]
  let K : Set (openFiber f U c) :=
    {y | g.edist p (incl y) ≤ ENNReal.ofReal (r + T / l)}
  let J : Set (openFiber f U c) :=
    {y | g.edist p (incl y) ≤ ENNReal.ofReal r}
  rw [mul_div_assoc] at hroom
  have hTdiv : 0 ≤ T / l := div_nonneg hT.le hl.le
  have hrR : r ≤ R := by linarith
  have hmidR : r + T / l ≤ R := by linarith
  have hcompact (a : ℝ) (ha : a ≤ R) :
      IsCompact {y : openFiber f U c | g.edist p (incl y) ≤ ENNReal.ofReal a} := by
    apply (isEmbedding_openFiberIncl f U c).isCompact_iff.mpr
    have he : incl '' {y | g.edist p (incl y) ≤ ENNReal.ofReal a} =
        {y | g.edist p y ≤ ENNReal.ofReal a} ∩ f ⁻¹' {c} := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨hz, z.2⟩
      · rintro ⟨hy, hfy⟩
        exact ⟨⟨⟨y, hball y (hy.trans (ENNReal.ofReal_le_ofReal ha))⟩, hfy⟩, hy, rfl⟩
    change IsCompact (incl '' {y | g.edist p (incl y) ≤ ENNReal.ofReal a})
    rw [he]
    exact (g.isCompact_closedBall_of_metricComplete hc p a).inter_right
      (isClosed_singleton.preimage hf.continuous)
  have hK : IsCompact K := hcompact (r + T / l) hmidR
  have hJ : IsCompact J := hcompact r hrR
  obtain ⟨V, δ, Φ, hV, hKV, hδ, hΦ, hinit, horbit, hflow, hstay⟩ :=
    g.exists_uniform_openFiber_normalizedGradient_manifoldFlow hc hf hφ U hreg c p
      hl hH (add_nonneg hr hTdiv) hT.le
      (show r + T / l + T / l ≤ R by linarith)
      hball (fun y => (hgrad y).1) hhess
  refine ⟨hregφ, ?_⟩
  intro t
  have hX := (normalizedGradient_smooth_of_regular DL hφL
    (fun y => hregφ y (mem_univ _))).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
  have hcover (s : ℝ) (hs : s ∈ Icc (t - T) t) :
      ∀ x ∈ J, φL x = t → ∃ y ∈ K, φL y = s ∧ Φ (t - s, y) = x := by
    intro x hx hxlevel
    have hτ : 0 ≤ t - s := sub_nonneg.mpr hs.2
    have hτT : t - s ≤ T := by linarith [hs.1]
    have hτroom : r + (t - s) / l ≤ R := by
      linarith [div_le_div_of_nonneg_right hτT hl.le]
    obtain ⟨ε, γ, hε, hγ, hend, hγorbit, hγbounds⟩ :=
      g.exists_openFiber_normalizedGradient_curve_ending_at hc hf hφ U hreg c p
        hl hH hr hτ hτroom hball (fun y => (hgrad y).1) hhess x hx
    have hzero : (0 : ℝ) ∈ Icc 0 (t - s) := ⟨le_rfl, hτ⟩
    have hstart := hγbounds 0 hzero
    have hyK : γ 0 ∈ K := by
      exact hstart.2.2.trans (ENNReal.ofReal_le_ofReal (by
        simp only [sub_zero]
        linarith [div_le_div_of_nonneg_right hτT hl.le]))
    have hys : φL (γ 0) = s := by
      have hval : φL (γ 0) = φL x - (t - s) + 0 := hstart.1
      rw [hxlevel] at hval
      linarith
    let η := min δ ε
    have hη : 0 < η := lt_min hδ hε
    have hsubΦ : Ioo (-η) (t - s + η) ⊆ Ioo (-δ) (T + δ) := by
      intro z hz
      constructor <;> linarith [hz.1, hz.2, min_le_left δ ε]
    have hsubγ : Ioo (-η) (t - s + η) ⊆ Ioo (-ε) (t - s + ε) := by
      intro z hz
      constructor <;> linarith [hz.1, hz.2, min_le_right δ ε]
    have heq := curve_eqOn_Ioo isOpen_univ hX.contMDiffOn
      (show (0 : ℝ) ∈ Ioo (-η) (t - s + η) by constructor <;> linarith)
      (fun _ _ => mem_univ _)
      ((horbit (γ 0) (hKV hyK)).mono hsubΦ) (hγorbit.mono hsubγ)
      (hinit (γ 0) (hKV hyK))
    refine ⟨γ 0, hyK, hys, ?_⟩
    exact (heq (show t - s ∈ Ioo (-η) (t - s + η) by constructor <;> linarith)).trans hend
  let A : ℝ → ℝ := fun s => (gL.regularLevelVolume hφL ⊤ hregφ s).real
    {z | openLevelIncl φL ⊤ s z ∈ K}
  let B : ℝ := (gL.regularLevelVolume hφL ⊤ hregφ t).real
    {z | openLevelIncl φL ⊤ t z ∈ J}
  obtain ⟨hAi, hcoarea⟩ := gL.integral_coarea_isCompact hφL ⊤ hregφ hK (subset_univ _)
  have hmass : ∀ s ∈ Icc (t - T) t,
      B ≤ Real.exp ((d : ℝ) * H * T / l ^ 2) * A s := by
    intro s hs
    have hτ : t - s ∈ Icc 0 T := ⟨sub_nonneg.mpr hs.2, by linarith [hs.1]⟩
    have hτopen : t - s ∈ Ioo (-δ) (T + δ) := by
      constructor <;> linarith [hτ.1, hτ.2]
    have hQ : ContMDiffOn (𝓡 (d + 1)) (𝓡 (d + 1)) ∞
        (fun y => Φ (t - s, y)) V := by
      intro y hy
      exact ((hΦ.contMDiffAt ((isOpen_Ioo.prod hV).mem_nhds ⟨hτopen, hy⟩)).comp y
        (contMDiffAt_const.prodMk contMDiffAt_id)).contMDiffWithinAt
    have hbound : ∀ y ∈ V, φL y = s → ∀ v : TangentSpace (𝓡 (d + 1)) y,
        mvfderiv (𝓡 (d + 1)) φL y v = 0 →
        gL.tangentNorm (Φ (t - s, y))
            (mfderiv (𝓡 (d + 1)) (𝓡 (d + 1)) (fun z => Φ (t - s, z)) y v) ≤
          Real.exp ((H / l ^ 2) * T) * gL.tangentNorm y v := by
      intro y hy _ v hv
      have hvb := tangentNorm_le_of_inner_exp_bound gL v
        (mfderiv (𝓡 (d + 1)) (𝓡 (d + 1)) (fun z => Φ (t - s, z)) y v)
        ((H / l ^ 2) * (t - s)) (by
          have he := (hflow y hy (t - s) hτ).2.2 v hv
          change gL.inner (Φ (t - s, y)) _ _ ≤
            gL.inner y v v * Real.exp (2 * (H / l ^ 2) * (t - s)) at he
          convert he using 1
          congr 2
          ring)
      apply hvb.trans
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hτ.2
        (div_nonneg hH (sq_nonneg l)))
    have hb := regularLevel_mass_le_of_smooth_image gL hφL hregφ hV hK hJ hKV hQ
      (Real.exp_pos ((H / l ^ 2) * T))
      (fun y hy hys => by
        have hval : φL (Φ (t - s, y)) = φL y + (t - s) := (hflow y hy _ hτ).1
        change φL y = s at hys
        change φL (Φ (t - s, y)) = t
        rw [hys] at hval
        linarith)
      (hcover s hs) hbound
    have hexp : Real.exp ((H / l ^ 2) * T) ^ d =
        Real.exp ((d : ℝ) * H * T / l ^ 2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hexp] at hb
    exact hb
  have hvolume : (∫ s, A s) ≤ gL.volumeMeasure.real K := by
    rw [← hcoarea]
    calc
      _ ≤ ∫ y in K, (1 : ℝ) ∂gL.volumeMeasure := by
        apply integral_mono_ae
          (ContinuousOn.integrableOn_compact hK
            (gL.continuous_tangentNorm_gradient hφL).continuousOn)
          (integrableOn_const (hs := hK.measure_ne_top))
        exact ae_restrict_of_forall_mem hK.measurableSet (fun y _ => (hgrad y).2)
      _ = _ := by simp
  exact scalar_le_of_integrable_slice_bound hAi (fun _ => ENNReal.toReal_nonneg)
    (Real.exp_pos _).le hT hmass hvolume
