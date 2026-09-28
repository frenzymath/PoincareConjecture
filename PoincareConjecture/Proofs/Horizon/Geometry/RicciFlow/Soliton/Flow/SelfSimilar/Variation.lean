import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.FlowIsometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Hessian.Symmetry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000

open Set Filter VectorField
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem coordinate_gradient_metric_derivative
    {D : LeviCivitaData g} {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (a : M)
    {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ (extChartAt (𝓡 n) a).target) (v w : EuclideanSpace ℝ (Fin n)) :
    let c := extChartAt (𝓡 n) a
    let B := g.pullbackCoefficients c.symm
    let G := mpullback (𝓡 n) (𝓡 n) c.symm (D.gradient f)
    fderiv ℝ B x (G x) v w + B x (fderiv ℝ G x v) w +
        B x v (fderiv ℝ G x w) =
      2 * D.hessian f (c.symm x)
        (mfderiv (𝓡 n) (𝓡 n) c.symm x v)
        (mfderiv (𝓡 n) (𝓡 n) c.symm x w) := by
  let c := extChartAt (𝓡 n) a
  let B := g.pullbackCoefficients c.symm
  let G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    mpullback (𝓡 n) (𝓡 n) c.symm (D.gradient f)
  have hc (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ c.target) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm y :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) a hy).contMDiffAt
      (extChartAt_target_mem_nhds' hy)
  have hi (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ c.target) :
      (mfderiv (𝓡 n) (𝓡 n) c.symm y).IsInvertible := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm hy
  obtain ⟨gE, DE, V, hVo, hxV, _, hE⟩ :=
    exists_local_realization (isOpen_extChartAt_target a) hx B
      (g.contDiffOn_chartCoefficients a) (fun y _ b d => g.symm _ _ _)
      (fun y hy b hb => by
        apply g.pos (c.symm y)
        intro hzero
        apply hb
        apply (hi y hy).injective
        rw [map_zero]
        exact hzero)
  have heq : gE.euclideanCoefficients =ᶠ[𝓝 x] B := by
    filter_upwards [hVo.mem_nhds hxV] with y hy
    exact hE y hy
  have hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) c.symm y).IsInvertible :=
    Filter.mem_of_superset (extChartAt_target_mem_nhds' hx) hi
  have hmetric : ∀ᶠ y in 𝓝 x, ∀ b d : EuclideanSpace ℝ (Fin n),
      gE.inner y b d = g.inner (c.symm y)
        (mfderiv (𝓡 n) (𝓡 n) c.symm y b)
        (mfderiv (𝓡 n) (𝓡 n) c.symm y d) := by
    filter_upwards [heq] with y hy b d
    exact congrArg (fun A => A b d) hy
  have hGd : DifferentiableAt ℝ G x :=
    (contDiffAt_mpullback_gradient hf a hx).differentiableAt (by simp)
  have hconn (b : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ G x b + coordinateChristoffel B x b (G x) =
        (mfderiv (𝓡 n) (𝓡 n) c.symm x).inverse
          (D.connection (D.gradient f) (c.symm x)
            (mfderiv (𝓡 n) (𝓡 n) c.symm x b)) := by
    have h := DE.connection_mpullback_of_metric_pullback D (hc x hx) hinv hmetric
      ((D.contMDiffAt_gradient (hf (c.symm x))).mdifferentiableAt (by simp)) b
    change DE.connection G x b = _ at h
    rw [DE.connection_eq_fderiv_add hGd] at h
    unfold LeviCivitaData.euclideanConnection at h
    rw [DE.connection_const_eq_inverse] at h
    change fderiv ℝ G x b + coordinateChristoffel gE.euclideanCoefficients x b (G x) = _ at h
    simpa only [coordinateChristoffel, heq.self_of_nhds, heq.fderiv_eq] using h
  have hBd : DifferentiableAt ℝ B x :=
    ((g.contDiffOn_chartCoefficients a).contDiffAt
      (extChartAt_target_mem_nhds' hx)).differentiableAt (by simp)
  have hBsymm : ∀ᶠ y in 𝓝 x, ∀ v w, B y v w = B y w v :=
    Filter.Eventually.of_forall (fun y v w => g.symm _ _ _)
  have hsymm (u v : EuclideanSpace ℝ (Fin n)) :
      coordinateChristoffel B x u v = coordinateChristoffel B x v u :=
    CoordinateExponential.christoffelBilinear_symm hBd hBsymm u v
  have hpair (b d : EuclideanSpace ℝ (Fin n)) :
      B x (fderiv ℝ G x b + coordinateChristoffel B x b (G x)) d =
        D.hessian f (c.symm x)
          (mfderiv (𝓡 n) (𝓡 n) c.symm x b)
          (mfderiv (𝓡 n) (𝓡 n) c.symm x d) := by
    rw [hconn, D.hessian_eq_inner_connection_gradient (hf (c.symm x))]
    change g.inner (c.symm x)
      (mfderiv (𝓡 n) (𝓡 n) c.symm x ((mfderiv (𝓡 n) (𝓡 n) c.symm x).inverse _)) _ = _
    rw [(hi x hx).self_apply_inverse]
    rfl
  dsimp only
  change fderiv ℝ B x (G x) v w + B x (fderiv ℝ G x v) w +
    B x v (fderiv ℝ G x w) = _
  rw [CoordinateExponential.fderiv_metric_eq_christoffel hBd
    (g.isInvertible_chartCoefficients a hx) hBsymm, hsymm (G x) v, hsymm (G x) w]
  have hv := hpair v w
  have hw := hpair w v
  rw [D.hessian_symm hf (c.symm x)
    (mfderiv (𝓡 n) (𝓡 n) c.symm x w)] at hw
  simp only [map_add, add_apply] at hv hw
  rw [hBsymm.self_of_nhds (coordinateChristoffel B x w (G x)),
    hBsymm.self_of_nhds (fderiv ℝ G x w)] at hw
  linarith

private theorem chartCoefficients_apply_chartDifferential
    (g : RiemannianMetric n M) (a : M) {y : M}
    (hy : y ∈ (extChartAt (𝓡 n) a).source) (v w : TangentSpace (𝓡 n) y) :
    g.pullbackCoefficients (extChartAt (𝓡 n) a).symm (extChartAt (𝓡 n) a y)
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) y v)
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) y w) = g.inner y v w := by
  have hid := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := 𝓡 n) hy
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hid
  have hidv := congrArg (fun L => L v) hid
  have hidw := congrArg (fun L => L w) hid
  simp only [ContinuousLinearMap.comp_apply] at hidv hidw
  change g.inner ((extChartAt (𝓡 n) a).symm (extChartAt (𝓡 n) a y))
    (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a).symm (extChartAt (𝓡 n) a y)
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) y v))
    (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a).symm (extChartAt (𝓡 n) a y)
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) y w)) = _
  rw [hidv, hidw]
  exact congrArg (fun z => g.inner z v w) ((extChartAt (𝓡 n) a).left_inv hy)

private theorem metric_pullback_in_charts
    {F : M → M} {x : M} (hF : ContMDiffAt (𝓡 n) (𝓡 n) ∞ F x)
    (a : M) (ha : F x ∈ (extChartAt (𝓡 n) a).source)
    (v w : TangentSpace (𝓡 n) x) :
    let c := extChartAt (𝓡 n) a
    let d := extChartAt (𝓡 n) x
    g.pullbackCoefficients c.symm (c (F x))
      (fderiv ℝ (c ∘ F ∘ d.symm) (d x) v)
      (fderiv ℝ (c ∘ F ∘ d.symm) (d x) w) =
        g.inner (F x) (mfderiv (𝓡 n) (𝓡 n) F x v) (mfderiv (𝓡 n) (𝓡 n) F x w) := by
  let c := extChartAt (𝓡 n) a
  let d := extChartAt (𝓡 n) x
  have hc : MDifferentiableAt (𝓡 n) (𝓡 n) c (F x) :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using ha)
  have hd : MDifferentiableAt (𝓡 n) (𝓡 n) d.symm (d x) :=
    ((contMDiffWithinAt_extChartAt_symm_target (I := 𝓡 n) (n := ∞) x
      (mem_extChartAt_target x)).contMDiffAt
        (extChartAt_target_mem_nhds x)).mdifferentiableAt (by simp)
  have hdid : mfderiv (𝓡 n) (𝓡 n) d.symm (d x) = ContinuousLinearMap.id ℝ _ := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      (mfderivWithin_range_extChartAt_symm (I := 𝓡 n) (x := x))
  have hFd : MDifferentiableAt (𝓡 n) (𝓡 n) F (d.symm (d x)) := by
    simpa only [d, extChartAt_to_inv] using hF.mdifferentiableAt (by simp)
  have hcd : MDifferentiableAt (𝓡 n) (𝓡 n) c (F (d.symm (d x))) := by
    simpa only [d, extChartAt_to_inv] using hc
  have hderiv := mfderiv_comp (d x) hcd (hFd.comp (d x) hd)
  rw [mfderiv_comp (d x) hFd hd, hdid, ContinuousLinearMap.comp_id] at hderiv
  rw [mfderiv_eq_fderiv] at hderiv
  change fderiv ℝ (c ∘ F ∘ d.symm) (d x) =
    (mfderiv (𝓡 n) (𝓡 n) c (F (d.symm (d x)))).comp
      (mfderiv (𝓡 n) (𝓡 n) F (d.symm (d x))) at hderiv
  rw [show d.symm (d x) = x from extChartAt_to_inv x] at hderiv
  dsimp only
  rw [hderiv]
  exact chartCoefficients_apply_chartDifferential g a ha _ _

theorem hasDerivAt_gradientFlow_metric_pairing
    {D : LeviCivitaData g} {f : M → ℝ} {Φ : ℝ → M → M}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ (fun z : ℝ × M => Φ z.1 z.2))
    (hΦ : ∀ x, IsMIntegralCurve (fun t => Φ t x) (D.gradient f))
    (x : M) (v w : TangentSpace (𝓡 n) x) (t : ℝ) :
    HasDerivAt (fun s => g.inner (Φ s x)
      (mfderiv (𝓡 n) (𝓡 n) (Φ s) x v) (mfderiv (𝓡 n) (𝓡 n) (Φ s) x w))
      (2 * D.hessian f (Φ t x)
        (mfderiv (𝓡 n) (𝓡 n) (Φ t) x v) (mfderiv (𝓡 n) (𝓡 n) (Φ t) x w)) t := by
  let c := extChartAt (𝓡 n) (Φ t x)
  let d := extChartAt (𝓡 n) x
  let q : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun z => c (Φ z.1 (d.symm z.2))
  let G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    mpullback (𝓡 n) (𝓡 n) c.symm (D.gradient f)
  let B := g.pullbackCoefficients c.symm
  have hdx : d.symm (d x) = x := extChartAt_to_inv x
  have hqt : q (t, d x) = c (Φ t x) := by simp only [q, hdx]
  have hct : q (t, d x) ∈ c.target := by rw [hqt]; exact mem_extChartAt_target _
  have hd : ContMDiffAt (𝓡 n) (𝓡 n) ∞ d.symm (d x) :=
    (contMDiffWithinAt_extChartAt_symm_target (I := 𝓡 n) (n := ∞) x
      (mem_extChartAt_target x)).contMDiffAt (extChartAt_target_mem_nhds x)
  have hfamily : ContMDiffAt 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) => Φ z.1 (d.symm z.2)) (t, d x) := by
    have hp : ContMDiffAt 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n))
        (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun z : ℝ × EuclideanSpace ℝ (Fin n) => (z.1, d.symm z.2)) (t, d x) :=
      (contMDiffAt_iff_contDiffAt.mpr contDiffAt_fst).prodMk
        (hd.comp (t, d x) (contMDiffAt_iff_contDiffAt.mpr contDiffAt_snd))
    exact (hs _).comp (t, d x) hp
  have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c (Φ t (d.symm (d x))) := by
    rw [hdx]
    exact contMDiffAt_extChartAt' (mem_chart_source _ _)
  have hq : ContDiffAt ℝ ∞ q (t, d x) :=
    contMDiffAt_iff_contDiffAt.mp (hc.comp (t, d x) hfamily)
  have hG : DifferentiableAt ℝ G (q (t, d x)) :=
    (contDiffAt_mpullback_gradient hf (Φ t x) hct).differentiableAt (by simp)
  have hB : DifferentiableAt ℝ B (q (t, d x)) :=
    ((g.contDiffOn_chartCoefficients (Φ t x)).contDiffAt
      (extChartAt_target_mem_nhds' hct)).differentiableAt (by simp)
  have hF (s : ℝ) : ContMDiff (𝓡 n) (𝓡 n) ∞ (Φ s) :=
    hs.comp (contMDiff_const.prodMk contMDiff_id)
  have hout : ∀ᶠ y in 𝓝 (d x), Φ t (d.symm y) ∈ c.source :=
    ((hF t _).comp (d x) hd).continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := 𝓡 n) (Φ t x)).mem_nhds
        (by simpa only [Function.comp_apply, hdx] using mem_extChartAt_source (I := 𝓡 n) (Φ t x)))
  have htime : ∀ᶠ y in 𝓝 (d x),
      HasDerivAt (fun s => q (s, y)) (G (q (t, y))) t := by
    filter_upwards [hout] with y hy
    have hh := hasDerivAt_chart_integralCurve (hΦ (d.symm y)) (Φ t x) t
      (by simpa only [c, extChartAt_source] using hy)
    have hgrad := mpullback_gradient_eq_chart_gradient (D := D) (f := f)
      (Φ t x) (c.map_source hy)
    change G (c (Φ t (d.symm y))) =
      mfderiv (𝓡 n) (𝓡 n) c (c.symm (c (Φ t (d.symm y))))
        (D.gradient f (c.symm (c (Φ t (d.symm y))))) at hgrad
    rw [c.left_inv hy] at hgrad
    change HasDerivAt (fun s => c (Φ s (d.symm y))) (G (c (Φ t (d.symm y)))) t
    rw [hgrad]
    exact hh
  have hqx : DifferentiableAt ℝ (fun y => q (t, y)) (d x) :=
    (hq.differentiableAt (by simp)).comp (d x)
      ((differentiableAt_const t).prodMk differentiableAt_id)
  have hcomp := (hG.hasFDerivAt.comp (d x) hqx.hasFDerivAt).fderiv
  simp only [Function.comp_def] at hcomp
  have hv := CoordinateExponential.hasDerivAt_variation hq htime v
  have hw := CoordinateExponential.hasDerivAt_variation hq htime w
  rw [hcomp] at hv hw
  have hBq : HasDerivAt (fun s => B (q (s, d x)))
      (fderiv ℝ B (q (t, d x)) (G (q (t, d x)))) t := by
    simpa only [Function.comp_def] using
      hB.hasFDerivAt.comp_hasDerivAt t htime.self_of_nhds
  have hm := (hBq.clm_apply hv).clm_apply hw
  have hmetric := coordinate_gradient_metric_derivative (D := D) hf (Φ t x) hct
    (fderiv ℝ (fun y => q (t, y)) (d x) v)
    (fderiv ℝ (fun y => q (t, y)) (d x) w)
  have hpoint : c.symm (q (t, d x)) = Φ t x := by rw [hqt]; exact extChartAt_to_inv _
  have hderiv : (mfderiv (𝓡 n) (𝓡 n) c.symm (q (t, d x))).comp
      (fderiv ℝ (fun y => q (t, y)) (d x)) = mfderiv (𝓡 n) (𝓡 n) (Φ t) x := by
    have hcancel : c.symm ∘ (fun y => q (t, y)) =ᶠ[𝓝 (d x)] Φ t ∘ d.symm := by
      filter_upwards [hout] with y hy
      exact c.left_inv hy
    have hcs := (contMDiffWithinAt_extChartAt_symm_target (I := 𝓡 n)
      (n := ∞) (Φ t x) hct).contMDiffAt (extChartAt_target_mem_nhds' hct)
    have heq := hcancel.mfderiv_eq (I := 𝓡 n) (I' := 𝓡 n)
    rw [mfderiv_comp (d x) (hcs.mdifferentiableAt (by simp))
      hqx.mdifferentiableAt, mfderiv_eq_fderiv] at heq
    rw [mfderiv_comp (d x) ((hF t).mdifferentiable (by simp) _)
      (hd.mdifferentiableAt (by simp))] at heq
    have hdi : mfderiv (𝓡 n) (𝓡 n) d.symm (d x) = ContinuousLinearMap.id ℝ _ := by
      simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
        (mfderivWithin_range_extChartAt_symm (I := 𝓡 n) (x := x))
    rw [hdi, ContinuousLinearMap.comp_id] at heq
    change (mfderiv (𝓡 n) (𝓡 n) c.symm (q (t, d x)) :
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).comp
        (fderiv ℝ (fun y => q (t, y)) (d x)) =
      (mfderiv (𝓡 n) (𝓡 n) (Φ t) (d.symm (d x)) :
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) at heq
    rw [hdx] at heq
    exact heq
  have hderivv := congrArg (fun L => L v) hderiv
  have hderivw := congrArg (fun L => L w) hderiv
  simp only [ContinuousLinearMap.comp_apply] at hderivv hderivw
  let H : M → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ := D.hessian f
  change fderiv ℝ B (q (t, d x)) (G (q (t, d x)))
      (fderiv ℝ (fun y => q (t, y)) (d x) v)
      (fderiv ℝ (fun y => q (t, y)) (d x) w) +
    B (q (t, d x)) (fderiv ℝ G (q (t, d x))
      (fderiv ℝ (fun y => q (t, y)) (d x) v))
      (fderiv ℝ (fun y => q (t, y)) (d x) w) +
    B (q (t, d x)) (fderiv ℝ (fun y => q (t, y)) (d x) v)
      (fderiv ℝ G (q (t, d x)) (fderiv ℝ (fun y => q (t, y)) (d x) w)) =
    2 * H (c.symm (q (t, d x)))
      (mfderiv (𝓡 n) (𝓡 n) c.symm (q (t, d x))
        (fderiv ℝ (fun y => q (t, y)) (d x) v))
      (mfderiv (𝓡 n) (𝓡 n) c.symm (q (t, d x))
        (fderiv ℝ (fun y => q (t, y)) (d x) w)) at hmetric
  erw [hpoint, hderivv, hderivw] at hmetric
  have hm' : HasDerivAt (fun s => B (q (s, d x))
      (fderiv ℝ (fun y => q (s, y)) (d x) v)
      (fderiv ℝ (fun y => q (s, y)) (d x) w))
      (2 * D.hessian f (Φ t x)
        (mfderiv (𝓡 n) (𝓡 n) (Φ t) x v) (mfderiv (𝓡 n) (𝓡 n) (Φ t) x w)) t := by
    apply hm.congr_deriv
    simp only [ContinuousLinearMap.comp_apply, add_apply]
    exact hmetric
  apply hm'.congr_of_eventuallyEq
  have ht : ContinuousAt (fun s => Φ s x) t :=
    (hs.comp (contMDiff_id.prodMk contMDiff_const)).continuous.continuousAt
  filter_upwards [ht.preimage_mem_nhds
    ((isOpen_extChartAt_source (I := 𝓡 n) (Φ t x)).mem_nhds
      (mem_extChartAt_source _))] with s hsx
  simpa +instances only [q, B, c, d, Function.comp_def, extChartAt_to_inv] using
    (metric_pullback_in_charts (g := g) (hF s x) (Φ t x) hsx v w).symm

end PoincareConjecture.RiemannianMetric
