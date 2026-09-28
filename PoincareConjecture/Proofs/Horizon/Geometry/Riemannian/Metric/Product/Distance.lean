import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.Complete










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle ENNReal Topology
private theorem riemannianEDist_map_le_of_norm_mfderiv_le
    {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace H M] [ChartedSpace H' N]
    [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
    [Bundle.RiemannianBundle (TangentSpace J : N → Type _)]
    {F : M → N} (hF : ContMDiff I J 1 F)
    (hbound : ∀ x (v : TangentSpace I x), ‖mfderiv I J F x v‖ ≤ ‖v‖)
    (x y : M) :
    Manifold.riemannianEDist J (F x) (F y) ≤ Manifold.riemannianEDist I x y := by
  apply le_of_forall_gt
  intro r hr
  obtain ⟨γ, h0, h1, hγ, hlen, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hr zero_lt_one
  have hle : Manifold.riemannianEDist J (F x) (F y) ≤
      Manifold.pathELength J (F ∘ γ) 0 1 :=
    Manifold.riemannianEDist_le_pathELength (hF.comp hγ).contMDiffOn
      (congrArg F h0) (congrArg F h1) zero_le_one
  have hlength : Manifold.pathELength J (F ∘ γ) 0 1 ≤
      Manifold.pathELength I γ 0 1 := by
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc,
      Manifold.pathELength_eq_lintegral_mfderiv_Icc]
    apply setLIntegral_mono' measurableSet_Icc
    intro t _
    rw [mfderiv_comp_apply t (hF.mdifferentiable one_ne_zero (γ t))
      (hγ.mdifferentiable one_ne_zero t)]
    exact enorm_le_iff_norm_le.mpr (hbound (γ t) _)
  exact (hle.trans hlength).trans_lt hlen

namespace PoincareConjecture.RiemannianMetric
variable {n : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) P] [IsManifold (𝓡 (n + 1)) ∞ P]
    (g : RiemannianMetric n M) (G : RiemannianMetric (n + 1) P)
    (e : (M × ℝ) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ, ℝ), 𝓡 (n + 1)⟯ P)
    (hmetric : ∀ (z : M × ℝ) (v w : TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) z),
      G.inner (e z)
        (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) e z v)
        (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) e z w) =
        g.inner z.1 v.1 w.1 + v.2 * w.2)
include hmetric in

theorem product_edist_bounds_of_pullback (x y : M × ℝ) :
    max (g.edist x.1 y.1) (EDist.edist x.2 y.2) ≤ G.edist (e x) (e y) ∧
      G.edist (e x) (e y) ≤ g.edist x.1 y.1 + EDist.edist x.2 y.2 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (n + 1)) : P → Type _) :=
    ⟨G.toRiemannianMetric⟩
  have hinv (z : P) (w : TangentSpace (𝓡 (n + 1)) z) :
      G.inner z w w =
        g.inner (e.symm z).1
          (mfderiv (𝓡 (n + 1)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) e.symm z w).1
          (mfderiv (𝓡 (n + 1)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) e.symm z w).1 +
        (mfderiv (𝓡 (n + 1)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) e.symm z w).2 ^ 2 := by
    have hc := mfderiv_comp z (e.contMDiff.mdifferentiable (by simp) _)
      (e.symm.contMDiff.mdifferentiable (by simp) _)
    have hid : (e ∘ e.symm : P → P) = id := by ext z; exact e.apply_symm_apply z
    rw [hid, mfderiv_id] at hc
    have hv := congrArg (fun A => A w) hc.symm
    have hh := hmetric (e.symm z)
      (mfderiv (𝓡 (n + 1)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) e.symm z w)
      (mfderiv (𝓡 (n + 1)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) e.symm z w)
    change mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) e (e.symm z)
      (mfderiv (𝓡 (n + 1)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) e.symm z w) = w at hv
    rw [hv] at hh
    rw [e.apply_symm_apply] at hh
    simpa only [pow_two] using hh
  have hf : ContMDiff (𝓡 (n + 1)) (𝓡 n) 1 (Prod.fst ∘ e.symm) :=
    contMDiff_fst.comp (e.symm.contMDiff.of_le (by simp))
  have hs : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) 1 (Prod.snd ∘ e.symm) :=
    contMDiff_snd.comp (e.symm.contMDiff.of_le (by simp))
  have hfst (z : P) (v : TangentSpace (𝓡 (n + 1)) z) :
      ‖mfderiv (𝓡 (n + 1)) (𝓡 n) (Prod.fst ∘ e.symm) z v‖ ≤ ‖v‖ := by
    rw [mfderiv_comp_apply z mdifferentiableAt_fst
      (e.symm.contMDiff.mdifferentiable (by simp) z), mfderiv_fst]
    rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
    change Real.sqrt (g.inner (e.symm z).1 _ _) ≤ Real.sqrt (G.inner z v v)
    rw [hinv]
    apply Real.sqrt_le_sqrt
    exact le_add_of_nonneg_right (sq_nonneg (mfderiv (𝓡 (n + 1)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) e.symm z v).2)
  have hsnd (z : P) (v : TangentSpace (𝓡 (n + 1)) z) :
      ‖mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) (Prod.snd ∘ e.symm) z v‖ ≤ ‖v‖ := by
    rw [mfderiv_comp_apply z mdifferentiableAt_snd
      (e.symm.contMDiff.mdifferentiable (by simp) z), mfderiv_snd]
    rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
    change Real.sqrt (_ * _) ≤ Real.sqrt (G.inner z v v)
    rw [hinv]
    apply Real.sqrt_le_sqrt
    have hnn : 0 ≤ g.inner (e.symm z).1
        (mfderiv (𝓡 (n + 1)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) e.symm z v).1
        (mfderiv (𝓡 (n + 1)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) e.symm z v).1 :=
      by
        by_cases hv : (mfderiv (𝓡 (n + 1)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) e.symm z v).1 = 0
        · rw [hv]; simp
        · exact (g.pos _ _ hv).le
    change (mfderiv (𝓡 (n + 1)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) e.symm z v).2 *
      (mfderiv (𝓡 (n + 1)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) e.symm z v).2 ≤ _
    nlinarith
  have hlower₁ := riemannianEDist_map_le_of_norm_mfderiv_le hf hfst (e x) (e y)
  have hlower₂ := riemannianEDist_map_le_of_norm_mfderiv_le hs hsnd (e x) (e y)
  have hhoriz (t : ℝ) (p q : M) : G.edist (e (p,t)) (e (q,t)) ≤ g.edist p q := by
    apply riemannianEDist_map_le_of_norm_mfderiv_le
      ((e.contMDiff.of_le (by simp)).comp (contMDiff_id.prodMk contMDiff_const))
    intro z v
    rw [mfderiv_comp_apply z (e.contMDiff.mdifferentiable (by simp) _)
      (mdifferentiableAt_id.prodMk mdifferentiableAt_const)]
    simp only [id_eq, mfderiv_prod_left]
    rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
    change Real.sqrt (G.inner (e (z,t)) _ _) ≤ Real.sqrt (g.inner z v v)
    rw [hmetric]
    change Real.sqrt (g.inner z v v + 0 * 0) ≤ Real.sqrt (g.inner z v v)
    simp
  have hvert (p : M) (s t : ℝ) : G.edist (e (p,s)) (e (p,t)) ≤ EDist.edist s t := by
    rw [IsRiemannianManifold.out (I := 𝓘(ℝ, ℝ))]
    apply riemannianEDist_map_le_of_norm_mfderiv_le
      ((e.contMDiff.of_le (by simp)).comp (contMDiff_const.prodMk contMDiff_id))
    intro z v
    rw [mfderiv_comp_apply z (e.contMDiff.mdifferentiable (by simp) _)
      (mdifferentiableAt_const.prodMk mdifferentiableAt_id)]
    simp only [id_eq, mfderiv_prod_right]
    rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
    change Real.sqrt (G.inner (e (p,z)) _ _) ≤ Real.sqrt ((show ℝ from v) * (show ℝ from v))
    rw [hmetric]
    change Real.sqrt (g.inner p 0 0 + (show ℝ from v) * (show ℝ from v)) ≤ Real.sqrt ((show ℝ from v) * (show ℝ from v))
    simp
  constructor
  · apply max_le
    · simpa only [Function.comp_apply, e.symm_apply_apply, RiemannianMetric.edist] using hlower₁
    · simpa only [Function.comp_apply, e.symm_apply_apply,
        ← IsRiemannianManifold.out (I := 𝓘(ℝ, ℝ)), RiemannianMetric.edist] using hlower₂
  · exact (show G.edist (e x) (e y) ≤
      G.edist (e x) (e (y.1,x.2)) + G.edist (e (y.1,x.2)) (e y) from
        Manifold.riemannianEDist_triangle).trans
      (add_le_add (hhoriz x.2 x.1 y.1) (hvert y.1 x.2 y.2))

include hmetric in

theorem metricComplete_of_product_pullback [T3Space M] [T3Space P]
    (hc : MetricComplete g) : MetricComplete G := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : CompleteSpace M := hc
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (n + 1)) : P → Type _) :=
    ⟨G.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (n + 1)))
      (TangentSpace (𝓡 (n + 1)) : P → Type _) :=
    ⟨⟨G.inner, G.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace P := EMetricSpace.ofRiemannianMetric (𝓡 (n + 1)) P
  have hLip : LipschitzWith 1 e.symm := by
    intro x y
    change max (g.edist (e.symm x).1 (e.symm y).1)
      (EDist.edist (e.symm x).2 (e.symm y).2) ≤ (1 : ℝ≥0∞) * G.edist x y
    simpa only [one_mul, e.apply_symm_apply] using
      (product_edist_bounds_of_pullback g G e hmetric (e.symm x) (e.symm y)).1
  apply EMetric.complete_of_cauchySeq_tendsto
  intro u hu
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete (hLip.uniformContinuous.comp_cauchySeq hu)
  refine ⟨e z, ?_⟩
  have hh := e.continuous.continuousAt.tendsto.comp hz
  simpa only [Function.comp_def, e.apply_symm_apply] using hh

include hmetric in

theorem product_half_cylinder_subset_ball (p : M) :
    e '' (g.ball p (1 / 2) ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)) ⊆
      G.ball (e (p, 0)) 1 := by
  rintro _ ⟨⟨x,t⟩, ⟨hx,ht⟩, rfl⟩
  have ht' : EDist.edist (0 : ℝ) t < ENNReal.ofReal (1 / 2) := by
    rw [edist_dist, Real.dist_eq, zero_sub, abs_neg]
    exact ENNReal.ofReal_lt_ofReal_iff (by norm_num) |>.2 (abs_lt.mpr ht)
  change G.edist (e (p,0)) (e (x,t)) < ENNReal.ofReal 1
  have h := (product_edist_bounds_of_pullback g G e hmetric (p,0) (x,t)).2
  exact h.trans_lt ((ENNReal.add_lt_add hx ht').trans_eq (by
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num))

end PoincareConjecture.RiemannianMetric
