import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Convexity.FlowContraction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Pullback
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.LocalExtension

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
open Set Filter VectorField
open Poincare.Geometry.Riemannian.Convexity
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

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

private theorem mpullback_eq_chart_field
    (X : (x : M) → TangentSpace (𝓡 n) x) (a : M)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ (extChartAt (𝓡 n) a).target) :
    mpullback (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a).symm X z =
      mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a)
        ((extChartAt (𝓡 n) a).symm z) (X ((extChartAt (𝓡 n) a).symm z)) := by
  let c := extChartAt (𝓡 n) a
  have hi : (mfderiv (𝓡 n) (𝓡 n) c.symm z).IsInvertible := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm hz
  have hcomp := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
    (I := 𝓡 n) (c.map_target hz)
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hcomp
  change (mfderiv (𝓡 n) (𝓡 n) c.symm (c (c.symm z))).comp
    (mfderiv (𝓡 n) (𝓡 n) c (c.symm z)) = ContinuousLinearMap.id ℝ _ at hcomp
  rw [c.right_inv hz] at hcomp
  apply hi.injective
  rw [mpullback, hi.self_apply_inverse]
  exact (congrArg (fun L => L (X (c.symm z))) hcomp).symm

private theorem hasDerivAt_chart_curve
    {X : (x : M) → TangentSpace (𝓡 n) x} {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ X) (p : M) (t : ℝ)
    (hp : γ t ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    HasDerivAt (fun u => extChartAt (𝓡 n) p (γ u))
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p) (γ t) (X (γ t))) t := by
  have hc := ((contMDiffAt_extChartAt' (I := 𝓡 n) (n := ∞) hp).mdifferentiableAt
    (by simp)).hasMFDerivAt
  have h := hc.comp t (hγ t)
  rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
  apply h.congr_mfderiv
  ext
  exact (congrArg (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p) (γ t))
    (one_smul ℝ (X (γ t)))).trans (one_smul ℝ _).symm

private theorem inverseChart_fderiv
    {F : M → M} {x : M} (hF : ContMDiffAt (𝓡 n) (𝓡 n) ∞ F x)
    (v : TangentSpace (𝓡 n) x) :
    let c := extChartAt (𝓡 n) (F x)
    let d := extChartAt (𝓡 n) x
    mfderiv (𝓡 n) (𝓡 n) c.symm (c (F x))
      (fderiv ℝ (c ∘ F ∘ d.symm) (d x) v) = mfderiv (𝓡 n) (𝓡 n) F x v := by
  let c := extChartAt (𝓡 n) (F x)
  let d := extChartAt (𝓡 n) x
  have hd : MDifferentiableAt (𝓡 n) (𝓡 n) d.symm (d x) :=
    ((contMDiffWithinAt_extChartAt_symm_target (I := 𝓡 n) (n := ∞) x
      (mem_extChartAt_target x)).contMDiffAt
        (extChartAt_target_mem_nhds x)).mdifferentiableAt (by simp)
  have hdx : d.symm (d x) = x := extChartAt_to_inv x
  have hdid : mfderiv (𝓡 n) (𝓡 n) d.symm (d x) = ContinuousLinearMap.id ℝ _ := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      (mfderivWithin_range_extChartAt_symm (I := 𝓡 n) (x := x))
  have hFd : MDifferentiableAt (𝓡 n) (𝓡 n) F (d.symm (d x)) := by
    rw [hdx]
    exact hF.mdifferentiableAt (by simp)
  have hcd : MDifferentiableAt (𝓡 n) (𝓡 n) c (F (d.symm (d x))) := by
    rw [hdx]
    exact mdifferentiableAt_extChartAt (mem_chart_source _ _)
  have he := mfderiv_comp (d x) hcd (hFd.comp (d x) hd)
  rw [mfderiv_comp (d x) hFd hd, hdid, ContinuousLinearMap.comp_id,
    mfderiv_eq_fderiv, hdx] at he
  simp only [Function.comp_apply] at he
  rw [hdx] at he
  dsimp only
  rw [he]
  have hinv := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
    (I := 𝓡 n) (mem_extChartAt_source (I := 𝓡 n) (F x))
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hinv
  exact congrArg (fun L => L (mfderiv (𝓡 n) (𝓡 n) F x v)) hinv

theorem hasDerivAt_manifoldFlow_squared_length
    (D : LeviCivitaData g)
    {X : (x : M) → TangentSpace (𝓡 n) x} {Φ : ℝ → M → M}
    (hX : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% X))
    (hs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ (Function.uncurry Φ))
    (hΦ : ∀ x, IsMIntegralCurve (I := 𝓡 n) (fun t => Φ t x) X)
    (x : M) (v : TangentSpace (𝓡 n) x) (t : ℝ) :
    let w := mfderiv (𝓡 n) (𝓡 n) (Φ t) x v
    HasDerivAt (fun s => g.inner (Φ s x)
      (mfderiv (𝓡 n) (𝓡 n) (Φ s) x v) (mfderiv (𝓡 n) (𝓡 n) (Φ s) x v))
      (2 * g.inner (Φ t x) (D.connection X (Φ t x) w) w) t := by
  let c := extChartAt (𝓡 n) (Φ t x)
  let d := extChartAt (𝓡 n) x
  let q : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun z => c (Φ z.1 (d.symm z.2))
  let G := mpullback (𝓡 n) (𝓡 n) c.symm X
  have hdx : d.symm (d x) = x := extChartAt_to_inv x
  have hqt : q (t, d x) = c (Φ t x) := by simp only [q, hdx]
  have hct : q (t, d x) ∈ c.target := by rw [hqt]; exact mem_extChartAt_target _
  have hd : ContMDiffAt (𝓡 n) (𝓡 n) ∞ d.symm (d x) :=
    (contMDiffWithinAt_extChartAt_symm_target (I := 𝓡 n) (n := ∞) x
      (mem_extChartAt_target x)).contMDiffAt (extChartAt_target_mem_nhds x)
  have hcs (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ c.target) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm z :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) (Φ t x) hz).contMDiffAt
      (extChartAt_target_mem_nhds' hz)
  have hi (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ c.target) :
      (mfderiv (𝓡 n) (𝓡 n) c.symm z).IsInvertible := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm hz
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
  have hG : DifferentiableAt ℝ G (q (t, d x)) := by
    have hp := (hX (c.symm (q (t, d x)))).mpullback_vectorField_preimage
      (hcs _ hct) (hi _ hct) (by simp)
    rw [Bundle.contMDiffAt_totalSpace] at hp
    exact (contMDiffAt_iff_contDiffAt.mp (by simpa using hp.2)).differentiableAt (by simp)
  have hF (s : ℝ) : ContMDiff (𝓡 n) (𝓡 n) ∞ (Φ s) :=
    hs.comp (contMDiff_const.prodMk contMDiff_id)
  have hout : ∀ᶠ y in 𝓝 (d x), Φ t (d.symm y) ∈ c.source :=
    ((hF t _).comp (d x) hd).continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := 𝓡 n) (Φ t x)).mem_nhds
        (by simpa only [Function.comp_apply, hdx] using mem_extChartAt_source (I := 𝓡 n) (Φ t x)))
  have htime : ∀ᶠ y in 𝓝 (d x),
      HasDerivAt (fun s => q (s, y)) (G (q (t, y))) t := by
    filter_upwards [hout] with y hy
    have hh := hasDerivAt_chart_curve (hΦ (d.symm y)) (Φ t x) t
      (by simpa only [c, extChartAt_source] using hy)
    have hfield := mpullback_eq_chart_field X (Φ t x) (c.map_source hy)
    change G (c (Φ t (d.symm y))) =
      mfderiv (𝓡 n) (𝓡 n) c (c.symm (c (Φ t (d.symm y))))
        (X (c.symm (c (Φ t (d.symm y))))) at hfield
    rw [c.left_inv hy] at hfield
    change HasDerivAt (fun s => c (Φ s (d.symm y))) (G (c (Φ t (d.symm y)))) t
    rw [hfield]
    exact hh
  obtain ⟨gE, DE, V, hVo, hqV, hVtarget, hE⟩ :=
    RiemannianMetric.exists_local_realization (isOpen_extChartAt_target (Φ t x)) hct
      (g.pullbackCoefficients c.symm) (g.contDiffOn_chartCoefficients (Φ t x))
      (fun z _ a b => g.symm _ _ _)
      (fun z hz a ha => by
        apply g.pos (c.symm z)
        intro hzero
        apply ha
        apply (hi z hz).injective
        rw [map_zero]
        exact hzero)
  have hmetric : ∀ᶠ z in 𝓝 (q (t, d x)), ∀ a b : EuclideanSpace ℝ (Fin n),
      gE.inner z a b = g.inner (c.symm z)
        (mfderiv (𝓡 n) (𝓡 n) c.symm z a) (mfderiv (𝓡 n) (𝓡 n) c.symm z b) := by
    filter_upwards [hVo.mem_nhds hqV] with z hz a b
    exact congrArg (fun B => B a b) (hE z hz)
  have hinv : ∀ᶠ z in 𝓝 (q (t, d x)),
      (mfderiv (𝓡 n) (𝓡 n) c.symm z).IsInvertible :=
    Filter.mem_of_superset (extChartAt_target_mem_nhds' hct) hi
  let w := fderiv ℝ (fun y => q (t, y)) (d x) v
  have hw : mfderiv (𝓡 n) (𝓡 n) c.symm (q (t, d x)) w =
      mfderiv (𝓡 n) (𝓡 n) (Φ t) x v := by
    rw [hqt]
    exact inverseChart_fderiv (hF t x) v
  have hconn := DE.connection_mpullback_of_metric_pullback D (hcs _ hct) hinv hmetric
    ((hX _).mdifferentiableAt (by simp)) w
  have hpair := hasDerivAt_flow_squared_length DE hq hG htime v
  dsimp only at hpair ⊢
  have hderivative : 2 * gE.inner (q (t, d x)) (DE.connection G (q (t, d x)) w) w =
      2 * g.inner (Φ t x)
        (D.connection X (Φ t x) (mfderiv (𝓡 n) (𝓡 n) (Φ t) x v))
        (mfderiv (𝓡 n) (𝓡 n) (Φ t) x v) := by
    rw [hconn, hmetric.self_of_nhds, (hi _ hct).self_apply_inverse, hw]
    rw [hqt, c.left_inv (mem_extChartAt_source (Φ t x))]
  have hpair' := hpair.congr_deriv hderivative
  apply hpair'.congr_of_eventuallyEq
  have ht : ContinuousAt (fun s => Φ s x) t :=
    (hs.comp (contMDiff_id.prodMk contMDiff_const)).continuous.continuousAt
  have hqtime : ContinuousAt (fun s => q (s, d x)) t := by
    have hp : Tendsto (fun s : ℝ => (s, d x)) (𝓝 t) (𝓝 (t, d x)) :=
      tendsto_id.prodMk_nhds tendsto_const_nhds
    exact (show Tendsto q (𝓝 (t, d x)) (𝓝 (q (t, d x))) from hq.continuousAt).comp hp
  filter_upwards [ht.preimage_mem_nhds
    ((isOpen_extChartAt_source (I := 𝓡 n) (Φ t x)).mem_nhds
      (mem_extChartAt_source _)), hqtime.preimage_mem_nhds (hVo.mem_nhds hqV)] with s hsx hsq
  have hm := hE (q (s, d x)) hsq
  change g.inner (Φ s x) _ _ = gE.euclideanCoefficients (q (s, d x)) _ _
  rw [hm]
  simpa +instances only [q, c, d, Function.comp_def, extChartAt_to_inv] using
    (metric_pullback_in_charts (g := g) (hF s x) (Φ t x) hsx v v).symm

end PoincareConjecture.LeviCivitaData
