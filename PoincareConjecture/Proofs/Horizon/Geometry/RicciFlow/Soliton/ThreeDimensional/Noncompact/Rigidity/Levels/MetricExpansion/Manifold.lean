import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.MetricExpansion.Flow
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Hessian.Chart
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Divergence.Pullback

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

private theorem gradient_pushforward_of_metric_pullback
    {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
    {g : RiemannianMetric n M} {h : RiemannianMetric n N}
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {F : M → N} {u : N → ℝ} {x : M}
    (hF : MDifferentiableAt (𝓡 n) (𝓡 n) F x)
    (hu : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) u (F x))
    (hinv : (mfderiv (𝓡 n) (𝓡 n) F x).IsInvertible)
    (hmetric : ∀ a b : TangentSpace (𝓡 n) x, g.inner x a b =
      h.inner (F x) (mfderiv (𝓡 n) (𝓡 n) F x a)
        (mfderiv (𝓡 n) (𝓡 n) F x b)) :
    mfderiv (𝓡 n) (𝓡 n) F x (D.gradient (u ∘ F) x) = D'.gradient u (F x) := by
  rw [D.gradient_comp_eq_mpullback D' hF hu hinv hmetric]
  exact hinv.self_apply_inverse _

private theorem normalizedGradient_metric_pullback
    {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
    {g : RiemannianMetric n M} {h : RiemannianMetric n N}
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {F : M → N} {u : N → ℝ} {x : M}
    (hF : MDifferentiableAt (𝓡 n) (𝓡 n) F x)
    (hu : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) u (F x))
    (hinv : (mfderiv (𝓡 n) (𝓡 n) F x).IsInvertible)
    (hmetric : ∀ a b : TangentSpace (𝓡 n) x, g.inner x a b =
      h.inner (F x) (mfderiv (𝓡 n) (𝓡 n) F x a)
        (mfderiv (𝓡 n) (𝓡 n) F x b)) :
    g.inner x (D.gradient (u ∘ F) x) (D.gradient (u ∘ F) x) =
        h.inner (F x) (D'.gradient u (F x)) (D'.gradient u (F x)) ∧
      mfderiv (𝓡 n) (𝓡 n) F x (D.normalizedGradient (u ∘ F) x) =
        D'.normalizedGradient u (F x) := by
  have hpush := gradient_pushforward_of_metric_pullback D D' hF hu hinv hmetric
  constructor
  · simp only [hmetric, hpush]
  · simp only [normalizedGradient, map_smul, hmetric, hpush]

end PoincareConjecture.LeviCivitaData

theorem PoincareConjecture.LeviCivitaData.exists_local_normalizedGradient_manifoldFlow_with_nondecreasing_metric
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : PoincareConjecture.RiemannianMetric n M} (D : PoincareConjecture.LeviCivitaData g)
    {f : M → ℝ} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    (hregular : ∀ y ∈ U, 0 < g.inner y (D.gradient f y) (D.gradient f y))
    (hhess : ∀ y ∈ U, ∀ v : TangentSpace (𝓡 n) y,
      mvfderiv (𝓡 n) f y v = 0 → 0 ≤ D.hessian f y v v)
    {x : M} (hx : x ∈ U) :
    ∃ (V : Set M) (δ : ℝ) (Φ : ℝ × M → M),
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ 0 < δ ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ Φ (Ioo (-δ) δ ×ˢ V) ∧
      (∀ y ∈ V, Φ (0, y) = y) ∧
      (∀ y ∈ V, (∀ t ∈ Ioo (-δ) δ, Φ (t, y) ∈ U) ∧
        IsMIntegralCurveOn (I := 𝓡 n) (fun t => Φ (t, y))
          (D.normalizedGradient f) (Ioo (-δ) δ)) ∧
      ∀ y ∈ V, ∀ t ∈ Ico 0 δ,
        f (Φ (t, y)) = f y + t ∧
        ∀ v : TangentSpace (𝓡 n) y, mvfderiv (𝓡 n) f y v = 0 →
          g.inner y v v ≤
          g.inner (Φ (t, y)) (mfderiv (𝓡 n) (𝓡 n) (fun z => Φ (t, z)) y v)
            (mfderiv (𝓡 n) (𝓡 n) (fun z => Φ (t, z)) y v) := by
  let c := extChartAt (𝓡 n) x
  have hc (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ c.target) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm z :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) x hz).contMDiffAt
      (extChartAt_target_mem_nhds' hz)
  have hi (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ c.target) :
      (mfderiv (𝓡 n) (𝓡 n) c.symm z).IsInvertible := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm hz
  have hchart : ContMDiffOn (𝓡 n) (𝓡 n) ∞ c c.source := by
    simpa only [c, extChartAt_source] using
      (contMDiffOn_extChartAt (I := 𝓡 n) (x := x) (n := ∞))
  obtain ⟨gE, DE, W, hWo, hxW, hWtarget, hE⟩ :=
    RiemannianMetric.exists_local_realization (isOpen_extChartAt_target x)
      (mem_extChartAt_target x) (g.pullbackCoefficients c.symm)
      (g.contDiffOn_chartCoefficients x) (fun z _ a b => g.symm _ _ _)
      (fun z hz v hv => by
        apply g.pos (c.symm z)
        intro hzero
        apply hv
        apply (hi z hz).injective
        rw [map_zero]
        exact hzero)
  let A := W ∩ c.symm ⁻¹' U
  have hAo : IsOpen A := by
    have hcs : ContinuousOn c.symm W := fun z hz =>
      (hc z (hWtarget hz)).continuousAt.continuousWithinAt
    exact hcs.isOpen_inter_preimage hWo hU
  have hxA : c x ∈ A := ⟨hxW, by change c.symm (c x) ∈ U; simpa only [c.left_inv (mem_extChartAt_source x)] using hx⟩
  have hAtarget : A ⊆ c.target := fun z hz => hWtarget hz.1
  have hAU (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ A) : c.symm z ∈ U := hz.2
  have hmetric (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ A)
      (v w : EuclideanSpace ℝ (Fin n)) :
      gE.inner z v w = g.inner (c.symm z)
        (mfderiv (𝓡 n) (𝓡 n) c.symm z v) (mfderiv (𝓡 n) (𝓡 n) c.symm z w) :=
    congrArg (fun B => B v w) (hE z hz.1)
  let fE := f ∘ c.symm
  have hfE : ContDiffOn ℝ ∞ fE A := by
    intro z hz
    exact (contMDiffAt_iff_contDiffAt.mp
      ((hf.contMDiffAt (hU.mem_nhds (hAU z hz))).comp z (hc z (hAtarget hz)))).contDiffWithinAt
  have hnatural (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ A) :
      gE.inner z (DE.gradient fE z) (DE.gradient fE z) =
          g.inner (c.symm z) (D.gradient f (c.symm z)) (D.gradient f (c.symm z)) ∧
        mfderiv (𝓡 n) (𝓡 n) c.symm z (DE.normalizedGradient fE z) =
          D.normalizedGradient f (c.symm z) :=
    normalizedGradient_metric_pullback DE D
      ((hc z (hAtarget hz)).mdifferentiableAt (by simp))
      ((hf.contMDiffAt (hU.mem_nhds (hAU z hz))).mdifferentiableAt (by simp))
      (hi z (hAtarget hz)) (hmetric z hz)
  have hregularE (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ A) :
      0 < gE.inner z (DE.gradient fE z) (DE.gradient fE z) := by
    rw [(hnatural z hz).1]
    exact hregular _ (hAU z hz)
  have hhessE (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ A)
      (v : EuclideanSpace ℝ (Fin n)) (hv : mvfderiv (𝓡 n) fE z v = 0) :
      0 ≤ DE.hessian fE z v v := by
    have hinv : ∀ᶠ w in 𝓝 z, (mfderiv (𝓡 n) (𝓡 n) c.symm w).IsInvertible := by
      filter_upwards [hAo.mem_nhds hz] with w hw
      exact hi w (hAtarget hw)
    have hm : ∀ᶠ w in 𝓝 z, ∀ a b : EuclideanSpace ℝ (Fin n),
        gE.inner w a b = g.inner (c.symm w)
          (mfderiv (𝓡 n) (𝓡 n) c.symm w a) (mfderiv (𝓡 n) (𝓡 n) c.symm w b) := by
      filter_upwards [hAo.mem_nhds hz] with w hw
      exact hmetric w hw
    rw [DE.hessian_comp_of_metric_pullback D (hc z (hAtarget hz)) hinv hm
      (hf.contMDiffAt (hU.mem_nhds (hAU z hz)))]
    apply hhess _ (hAU z hz)
    have he := congrArg (fun L => L v) (mvfderiv_comp z
      ((hf.contMDiffAt (hU.mem_nhds (hAU z hz))).mdifferentiableAt (by simp))
      ((hc z (hAtarget hz)).mdifferentiableAt (by simp)))
    exact he.symm.trans hv
  obtain ⟨B, δ, q, hBo, hxB, hBA, hδ, hq, hq0, hqtime, hqbound⟩ :=
    DE.exists_local_normalizedGradient_flow_with_nondecreasing_metric hAo hfE hregularE hhessE hxA
  let V := c.source ∩ c ⁻¹' B
  have hVo : IsOpen V := hchart.continuousOn.isOpen_inter_preimage
    (isOpen_extChartAt_source x) hBo
  have hxV : x ∈ V := ⟨mem_extChartAt_source x, hxB⟩
  have hVU : V ⊆ U := by
    intro y hy
    have h := hAU (c y) (hBA hy.2)
    simpa only [c.left_inv hy.1] using h
  let Φ : ℝ × M → M := fun z => c.symm (q (z.1, c z.2))
  have hqpoint (t : ℝ) (y : M) (hy : y ∈ V) (ht : t ∈ Ioo (-δ) δ) :
      q (t, c y) ∈ A := (hqtime (c y) hy.2 t ht).1
  have hqd (t : ℝ) (y : M) (hy : y ∈ V) (ht : t ∈ Ioo (-δ) δ) :
      ContDiffAt ℝ ∞ q (t, c y) :=
    hq.contDiffAt ((isOpen_Ioo.prod hBo).mem_nhds ⟨ht, hy.2⟩)
  have hcd (y : M) (hy : y ∈ V) : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c y :=
    hchart.contMDiffAt (extChartAt_source_mem_nhds' hy.1)
  have hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ Φ (Ioo (-δ) δ ×ˢ V) := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    have hpair : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n))
        (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞ (fun z : ℝ × M => (z.1, c z.2)) (t, y) :=
      contMDiffAt_fst.prodMk ((hcd y hy).comp (t, y) contMDiffAt_snd)
    have hqm : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ q (t, c y) := by
      rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
      exact (hqd t y hy ht).contMDiffAt
    exact ((hc _ (hAtarget (hqpoint t y hy ht))).comp (t, y)
      (hqm.comp (t, y) hpair)).contMDiffWithinAt
  refine ⟨V, δ, Φ, hVo, hxV, hVU, hδ, hΦ, ?_, ?_, ?_⟩
  · intro y hy
    change c.symm (q (0, c y)) = y
    rw [hq0 _ hy.2, c.left_inv hy.1]
  · intro y hy
    refine ⟨fun t ht => hAU _ (hqpoint t y hy ht), ?_⟩
    intro t ht
    have htime := (hqtime _ hy.2 t ht).2.hasFDerivAt.hasMFDerivAt
    have hcderiv := ((hc _ (hAtarget (hqpoint t y hy ht))).mdifferentiableAt
      (by simp)).hasMFDerivAt
    have hd := hcderiv.comp t htime
    apply HasMFDerivAt.hasMFDerivWithinAt
    apply hd.congr_mfderiv
    apply ContinuousLinearMap.ext
    intro a
    change (mfderiv (𝓡 n) (𝓡 n) c.symm (q (t, c y)))
        (a • DE.normalizedGradient fE (q (t, c y))) =
      a • D.normalizedGradient f (c.symm (q (t, c y)))
    rw [map_smul, (hnatural _ (hqpoint t y hy ht)).2]
  · intro y hy t ht
    have ht' : t ∈ Ioo (-δ) δ := ⟨by linarith [ht.1], ht.2⟩
    refine ⟨?_, ?_⟩
    · have he := (hqbound (c y) hy.2 t ht).1
      simpa only [fE, Function.comp_apply, c.left_inv hy.1] using he
    · intro v hv
      let w := mfderiv (𝓡 n) (𝓡 n) c y v
      have hinverse : mfderiv (𝓡 n) (𝓡 n) c.symm (c y) w = v := by
        have he := congrArg (fun L => L v)
          (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hy.1)
        simpa +instances only [ModelWithCorners.range_eq_univ, mfderivWithin_univ,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using! he
      have hfinv : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f (c.symm (c y)) :=
        hf.contMDiffAt (hU.mem_nhds (hAU _ (hBA hy.2)))
      have hw : mvfderiv (𝓡 n) fE (c y) w = 0 := by
        have he := congrArg (fun L => L w) (mvfderiv_comp (c y)
          (hfinv.mdifferentiableAt (by simp))
          ((hc _ (hAtarget (hBA hy.2))).mdifferentiableAt (by simp)))
        change mvfderiv (𝓡 n) fE (c y) w =
          mvfderiv (𝓡 n) f (c.symm (c y))
            (mfderiv (𝓡 n) (𝓡 n) c.symm (c y) w) at he
        rw [hinverse] at he
        rw [c.left_inv hy.1] at he
        exact he.trans hv
      have hmetric0 : gE.inner (c y) w w = g.inner y v v := by
        have hm := hmetric (c y) (hBA hy.2) w w
        rw [hinverse, c.left_inv hy.1] at hm
        exact hm
      have hqt : ContDiffAt ℝ ∞ (fun z => q (t, z)) (c y) :=
        (hqd t y hy ht').comp (c y) (contDiffAt_const.prodMk contDiffAt_id)
      have hinner : MDifferentiableAt (𝓡 n) (𝓡 n) (fun z => q (t, c z)) y :=
        hqt.contMDiffAt.mdifferentiableAt (by simp) |>.comp y
          ((hcd y hy).mdifferentiableAt (by simp))
      have houter := (hc _ (hAtarget (hqpoint t y hy ht'))).mdifferentiableAt (by simp)
      have hspatial : mfderiv (𝓡 n) (𝓡 n) (fun z => Φ (t, z)) y v =
          mfderiv (𝓡 n) (𝓡 n) c.symm (q (t, c y))
            (fderiv ℝ (fun z => q (t, z)) (c y) w) := by
        have he := mfderiv_comp y houter hinner
        have he' := mfderiv_comp y (hqt.contMDiffAt.mdifferentiableAt (by simp))
          ((hcd y hy).mdifferentiableAt (by simp))
        change mfderiv (𝓡 n) (𝓡 n) (fun z => q (t, c z)) y =
          (mfderiv (𝓡 n) (𝓡 n) (fun z => q (t, z)) (c y)).comp
            (mfderiv (𝓡 n) (𝓡 n) c y) at he'
        have hvalue := congrArg (fun L => L v) he
        rw [he'] at hvalue
        change mfderiv (𝓡 n) (𝓡 n) (fun z => Φ (t, z)) y v =
          mfderiv (𝓡 n) (𝓡 n) c.symm (q (t, c y))
            (mfderiv (𝓡 n) (𝓡 n) (fun z => q (t, z)) (c y) w) at hvalue
        rw [mfderiv_eq_fderiv] at hvalue
        exact hvalue
      have he := (hqbound (c y) hy.2 t ht).2 w hw
      rw [hmetric0, hmetric _ (hqpoint t y hy ht')] at he
      simpa only [hspatial] using he
