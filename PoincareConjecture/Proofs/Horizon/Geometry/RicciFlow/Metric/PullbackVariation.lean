import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Coordinates.Coefficients
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Flow.SelfSimilar.Variation








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000

open Set Filter VectorField
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

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
    (g : RiemannianMetric n M) {Ψ : M → M} {x : M}
    (hΨ : ContMDiffAt (𝓡 n) (𝓡 n) ∞ Ψ x)
    (a : M) (ha : Ψ x ∈ (extChartAt (𝓡 n) a).source)
    (v w : TangentSpace (𝓡 n) x) :
    let c := extChartAt (𝓡 n) a
    let d := extChartAt (𝓡 n) x
    g.pullbackCoefficients c.symm (c (Ψ x))
      (fderiv ℝ (c ∘ Ψ ∘ d.symm) (d x) v)
      (fderiv ℝ (c ∘ Ψ ∘ d.symm) (d x) w) =
        g.inner (Ψ x) (mfderiv (𝓡 n) (𝓡 n) Ψ x v) (mfderiv (𝓡 n) (𝓡 n) Ψ x w) := by
  let c := extChartAt (𝓡 n) a
  let d := extChartAt (𝓡 n) x
  have hc : MDifferentiableAt (𝓡 n) (𝓡 n) c (Ψ x) :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using ha)
  have hd : MDifferentiableAt (𝓡 n) (𝓡 n) d.symm (d x) :=
    ((contMDiffWithinAt_extChartAt_symm_target (I := 𝓡 n) (n := ∞) x
      (mem_extChartAt_target x)).contMDiffAt
        (extChartAt_target_mem_nhds x)).mdifferentiableAt (by simp)
  have hdid : mfderiv (𝓡 n) (𝓡 n) d.symm (d x) = ContinuousLinearMap.id ℝ _ := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      (mfderivWithin_range_extChartAt_symm (I := 𝓡 n) (x := x))
  have hΨd : MDifferentiableAt (𝓡 n) (𝓡 n) Ψ (d.symm (d x)) := by
    simpa only [d, extChartAt_to_inv] using hΨ.mdifferentiableAt (by simp)
  have hcd : MDifferentiableAt (𝓡 n) (𝓡 n) c (Ψ (d.symm (d x))) := by
    simpa only [d, extChartAt_to_inv] using hc
  have hderiv := mfderiv_comp (d x) hcd (hΨd.comp (d x) hd)
  rw [mfderiv_comp (d x) hΨd hd, hdid, ContinuousLinearMap.comp_id] at hderiv
  rw [mfderiv_eq_fderiv] at hderiv
  change fderiv ℝ (c ∘ Ψ ∘ d.symm) (d x) =
    (mfderiv (𝓡 n) (𝓡 n) c (Ψ (d.symm (d x)))).comp
      (mfderiv (𝓡 n) (𝓡 n) Ψ (d.symm (d x))) at hderiv
  rw [show d.symm (d x) = x from extChartAt_to_inv x] at hderiv
  dsimp only
  rw [hderiv]
  exact chartCoefficients_apply_chartDifferential g a ha _ _

variable {J : Set ℝ} (F : RicciFlow n M J)



theorem hasDerivAt_negativeGradient_pullback_metric
    (hJ : IsOpen J) {f : ℝ × M → ℝ} {Φ : ℝ → M → M}
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ f (J ×ˢ univ))
    (hs : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
      (fun z : ℝ × M => Φ z.1 z.2) (J ×ˢ univ))
    (hΦ : ∀ s ∈ J, ∀ y, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 n) (fun r => Φ r y) s
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (-((F.connection s).gradient (fun z => f (s, z)) (Φ s y)))))
    {t : ℝ} (ht : t ∈ J) (x : M) (v w : TangentSpace (𝓡 n) x) :
    HasDerivAt (fun s => (F.metric s).inner (Φ s x)
      (mfderiv (𝓡 n) (𝓡 n) (Φ s) x v) (mfderiv (𝓡 n) (𝓡 n) (Φ s) x w))
      (-2 * (F.connection t).ricci (Φ t x)
          (mfderiv (𝓡 n) (𝓡 n) (Φ t) x v) (mfderiv (𝓡 n) (𝓡 n) (Φ t) x w) -
        2 * (F.connection t).hessian (fun y => f (t, y)) (Φ t x)
          (mfderiv (𝓡 n) (𝓡 n) (Φ t) x v) (mfderiv (𝓡 n) (𝓡 n) (Φ t) x w)) t := by
  let c := extChartAt (𝓡 n) (Φ t x)
  let d := extChartAt (𝓡 n) x
  let q : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun z => c (Φ z.1 (d.symm z.2))
  let G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    mpullback (𝓡 n) (𝓡 n) c.symm ((F.connection t).gradient (fun y => f (t, y)))
  let B : ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    fun z => (F.metric z.1).pullbackCoefficients c.symm z.2
  have hsAt {s : ℝ} (hsJ : s ∈ J) (y : M) :
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
        (fun z : ℝ × M => Φ z.1 z.2) (s, y) :=
    hs.contMDiffAt ((hJ.prod isOpen_univ).mem_nhds ⟨hsJ, mem_univ y⟩)
  have hF {s : ℝ} (hsJ : s ∈ J) : ContMDiff (𝓡 n) (𝓡 n) ∞ (Φ s) :=
    fun y => (hsAt hsJ y).comp y (contMDiffAt_const.prodMk contMDiffAt_id)
  have hft : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => f (t, y)) :=
    fun y => (hf.contMDiffAt ((hJ.prod isOpen_univ).mem_nhds ⟨ht, mem_univ y⟩)).comp
      y (contMDiffAt_const.prodMk contMDiffAt_id)
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
    exact (hsAt ht _).comp (t, d x) hp
  have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c (Φ t (d.symm (d x))) := by
    rw [hdx]
    exact contMDiffAt_extChartAt' (mem_chart_source _ _)
  have hq : ContDiffAt ℝ ∞ q (t, d x) :=
    contMDiffAt_iff_contDiffAt.mp (hc.comp (t, d x) hfamily)
  have hG : DifferentiableAt ℝ G (q (t, d x)) :=
    (RiemannianMetric.contDiffAt_mpullback_gradient hft (Φ t x) hct).differentiableAt (by simp)
  have hB : DifferentiableAt ℝ B (t, q (t, d x)) :=
    ((F.contDiffOn_pullbackCoefficients hJ (isOpen_extChartAt_target (Φ t x))
      (contMDiffOn_extChartAt_symm (I := 𝓡 n) (Φ t x))).contDiffAt
      ((hJ.prod (isOpen_extChartAt_target (Φ t x))).mem_nhds ⟨ht, hct⟩)).differentiableAt (by simp)
  have hout : ∀ᶠ y in 𝓝 (d x), Φ t (d.symm y) ∈ c.source :=
    ((hF ht _).comp (d x) hd).continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := 𝓡 n) (Φ t x)).mem_nhds
        (by simpa only [Function.comp_apply, hdx] using mem_extChartAt_source (I := 𝓡 n) (Φ t x)))
  have htime : ∀ᶠ y in 𝓝 (d x),
      HasDerivAt (fun s => q (s, y)) (-G (q (t, y))) t := by
    filter_upwards [hout] with y hy
    have hc' := ((contMDiffAt_extChartAt' (I := 𝓡 n) (n := ∞)
      (by simpa only [c, extChartAt_source] using hy)).mdifferentiableAt (by simp)).hasMFDerivAt
    have hh := hc'.comp t (hΦ t ht (d.symm y))
    have hgrad := RiemannianMetric.mpullback_gradient_eq_chart_gradient
      (D := F.connection t) (f := fun z => f (t, z)) (Φ t x) (c.map_source hy)
    change G (c (Φ t (d.symm y))) =
      mfderiv (𝓡 n) (𝓡 n) c (c.symm (c (Φ t (d.symm y))))
        ((F.connection t).gradient (fun z => f (t, z))
          (c.symm (c (Φ t (d.symm y))))) at hgrad
    rw [c.left_inv hy] at hgrad
    change HasDerivAt (fun s => c (Φ s (d.symm y))) (-G (c (Φ t (d.symm y)))) t
    rw [hgrad, hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
    apply hh.congr_mfderiv
    ext
    change (mfderiv (𝓡 n) (𝓡 n) c (Φ t (d.symm y)))
      ((1 : ℝ) • -((F.connection t).gradient (fun z => f (t, z)) (Φ t (d.symm y)))) =
        (1 : ℝ) • -((mfderiv (𝓡 n) (𝓡 n) c (Φ t (d.symm y)))
          ((F.connection t).gradient (fun z => f (t, z)) (Φ t (d.symm y))))
    simp only [one_smul, map_neg]
  have hqx : DifferentiableAt ℝ (fun y => q (t, y)) (d x) :=
    (hq.differentiableAt (by simp)).comp (d x)
      ((differentiableAt_const t).prodMk differentiableAt_id)
  have hcomp : fderiv ℝ (fun y => -G (q (t, y))) (d x) =
      -((fderiv ℝ G (q (t, d x))).comp (fderiv ℝ (fun y => q (t, y)) (d x))) := by
    rw [fderiv_fun_neg]
    congr 1
    simpa only [Function.comp_def] using (hG.hasFDerivAt.comp (d x) hqx.hasFDerivAt).fderiv
  have hv := CoordinateExponential.hasDerivAt_variation hq htime v
  have hw := CoordinateExponential.hasDerivAt_variation hq htime w
  rw [hcomp] at hv hw
  have hBq := hB.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk htime.self_of_nhds)
  have hm := (hBq.clm_apply hv).clm_apply hw
  have hspace := (hB.hasFDerivAt.comp (q (t, d x))
    ((hasFDerivAt_const (c := t) _).prodMk (hasFDerivAt_id _))).fderiv
  have hmetric := RiemannianMetric.coordinate_gradient_metric_derivative
    (D := F.connection t) hft (Φ t x) hct
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
    rw [mfderiv_comp (d x) ((hF ht).mdifferentiable (by simp) _)
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
  have hBt := hB.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t (q (t, d x))))
  have hBtvw := (hBt.clm_apply (hasDerivAt_const t
    (fderiv ℝ (fun y => q (t, y)) (d x) v))).clm_apply
    (hasDerivAt_const t (fderiv ℝ (fun y => q (t, y)) (d x) w))
  have hRic := ((F.equation t ht (c.symm (q (t, d x)))
    (mfderiv (𝓡 n) (𝓡 n) c.symm (q (t, d x))
      (fderiv ℝ (fun y => q (t, y)) (d x) v))
    (mfderiv (𝓡 n) (𝓡 n) c.symm (q (t, d x))
      (fderiv ℝ (fun y => q (t, y)) (d x) w))).hasDerivAt (hJ.mem_nhds ht)).unique hBtvw
  simp only [map_zero, add_zero] at hRic
  erw [hpoint, hderivv, hderivw] at hRic
  let H : M → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ :=
    (F.connection t).hessian (fun y => f (t, y))
  change fderiv ℝ (fun y => B (t, y)) (q (t, d x)) (G (q (t, d x)))
      (fderiv ℝ (fun y => q (t, y)) (d x) v)
      (fderiv ℝ (fun y => q (t, y)) (d x) w) +
    B (t, q (t, d x)) (fderiv ℝ G (q (t, d x))
      (fderiv ℝ (fun y => q (t, y)) (d x) v))
      (fderiv ℝ (fun y => q (t, y)) (d x) w) +
    B (t, q (t, d x)) (fderiv ℝ (fun y => q (t, y)) (d x) v)
      (fderiv ℝ G (q (t, d x)) (fderiv ℝ (fun y => q (t, y)) (d x) w)) =
    2 * H (c.symm (q (t, d x)))
      (mfderiv (𝓡 n) (𝓡 n) c.symm (q (t, d x))
        (fderiv ℝ (fun y => q (t, y)) (d x) v))
      (mfderiv (𝓡 n) (𝓡 n) c.symm (q (t, d x))
        (fderiv ℝ (fun y => q (t, y)) (d x) w)) at hmetric
  erw [hpoint, hderivv, hderivw] at hmetric
  have hspace' := congrArg (fun L => L (G (q (t, d x)))) hspace
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply] at hspace'
  have hsplit : ((1 : ℝ), -G (q (t, d x))) =
      (1, (0 : EuclideanSpace ℝ (Fin n))) - (0, G (q (t, d x))) := by simp
  have hm' := hm.congr_deriv (show _ =
      -2 * (F.connection t).ricci (Φ t x)
        (mfderiv (𝓡 n) (𝓡 n) (Φ t) x v) (mfderiv (𝓡 n) (𝓡 n) (Φ t) x w) -
      2 * (F.connection t).hessian (fun y => f (t, y)) (Φ t x)
        (mfderiv (𝓡 n) (𝓡 n) (Φ t) x v) (mfderiv (𝓡 n) (𝓡 n) (Φ t) x w) from by
    simp only [ContinuousLinearMap.comp_apply, neg_apply, map_neg, add_apply]
    erw [hsplit, map_sub]
    simp only [sub_apply]
    erw [← hspace']
    dsimp only [H, Function.comp_def, id_eq] at hmetric ⊢
    linear_combination -hRic - hmetric)
  apply hm'.congr_of_eventuallyEq
  have htx : ContinuousAt (fun s => Φ s x) t := by
    have hi : ContinuousAt (fun s : ℝ => (s, x)) t :=
      continuousAt_id.prodMk continuousAt_const
    have h := Filter.Tendsto.comp (hsAt ht x).continuousAt hi
    exact h
  filter_upwards [hJ.mem_nhds ht, htx.preimage_mem_nhds
    ((isOpen_extChartAt_source (I := 𝓡 n) (Φ t x)).mem_nhds
      (mem_extChartAt_source _))] with s hsJ hsx
  simpa +instances only [q, B, c, d, Function.comp_def, extChartAt_to_inv, id_eq] using
    (metric_pullback_in_charts (F.metric s) (hF hsJ x) (Φ t x) hsx v w).symm

end PoincareConjecture.RicciFlow
