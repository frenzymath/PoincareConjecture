import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Smoothing.Basepoint.Euclidean
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Smoothing.Charts.Perturbation
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Distance.PathBounds
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Exact point correction on a Riemannian manifold

Conjugate a supported coordinate correction and its homotopy by a smooth
chart. Compact support controls the chart boundary uniformly in time.
The metric estimate uses the actual pullback tangent norm. This is the
exact-basepoint step of the 2026-09-18 SurgeryComparison.Transport quantitative approximation
contract following Morgan-Tian Claim 18.22, printed p. 433. The derivation
is `proof-work/tasks/SurgeryComparison.Transport/derivations/2026-09-20-helper-point-correction-manifold.md`.
-/

set_option autoImplicit false

open Function Set Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal unitInterval Bundle

namespace PoincareMT.SurgeryComparison.Transport

section ChartCorrection

variable {M E A : Type*} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace A]

/-- Conjugate a coordinate correction on its chart and use the identity
elsewhere; SurgeryComparison.Transport exact-point correction, Claim 18.22, p. 433. -/
noncomputable def chartCorrection (e : OpenPartialHomeomorph M E) (f : E → E) : M → M :=
  chartPerturb e e.source id (fun x => f (e x) - e x)

/-- The chart correction has its conjugation formula on the chart
source; SurgeryComparison.Transport point-correction derivation, Claim 18.22, p. 433. -/
theorem chartCorrection_of_mem (e : OpenPartialHomeomorph M E) (f : E → E)
    {x : M} (hx : x ∈ e.source) : chartCorrection e f x = e.symm (f (e x)) := by
  rw [chartCorrection, chartPerturb_of_mem e e.source id _ hx]
  congr 1
  dsimp only [id_eq]
  abel

/-- Outside the chart source the correction is the identity; SurgeryComparison.Transport
point-correction derivation, Claim 18.22, p. 433. -/
theorem chartCorrection_of_not_mem (e : OpenPartialHomeomorph M E) (f : E → E)
    {x : M} (hx : x ∉ e.source) : chartCorrection e f x = x := by
  simp [chartCorrection, chartPerturb, hx]

/-- A coordinate map fixed off `K` gives a manifold map fixed off the
inverse-chart image of `K`; Claim 18.22, p. 433. -/
theorem chartCorrection_eq_self (e : OpenPartialHomeomorph M E) {f : E → E} {K : Set E}
    (hfix : ∀ z ∉ K, f z = z) {x : M} (hx : x ∉ e.symm '' K) :
    chartCorrection e f x = x := by
  by_cases hxs : x ∈ e.source
  · have hex : e x ∉ K := fun h => hx ⟨e x, h, e.left_inv hxs⟩
    rw [chartCorrection_of_mem e f hxs, hfix _ hex, e.left_inv hxs]
  · exact chartCorrection_of_not_mem e f hxs

/-- The compact support's inverse-chart image controls a neighborhood
on which the manifold correction is the identity; Claim 18.22, p. 433. -/
theorem chartCorrection_eventuallyEq (e : OpenPartialHomeomorph M E)
    {f : E → E} {K : Set E} (hK : IsCompact K) (hKe : K ⊆ e.target)
    (hfix : ∀ z ∉ K, f z = z) {x : M} (hx : x ∉ e.symm '' K) :
    chartCorrection e f =ᶠ[𝓝 x] id := by
  have hc : IsCompact (e.symm '' K) :=
    hK.image_of_continuousOn (e.continuousOn_symm.mono hKe)
  filter_upwards [hc.isClosed.isOpen_compl.mem_nhds hx] with y hy
  exact chartCorrection_eq_self e hfix hy

/-- A continuous family of supported coordinate corrections conjugates
to a continuous family on the manifold. The compact support is common to
every parameter; SurgeryComparison.Transport homotopy gluing, Claim 18.22, p. 433. -/
theorem continuous_chartCorrection_family (e : OpenPartialHomeomorph M E)
    {F : A → E → E} (hF : Continuous (uncurry F))
    {K : Set E} (hK : IsCompact K) (hKe : K ⊆ e.target)
    (hrange : ∀ a, MapsTo (F a) e.target e.target)
    (hfix : ∀ a z, z ∉ K → F a z = z) :
    Continuous (fun p : A × M => chartCorrection e (F p.1) p.2) := by
  have hc : IsCompact (e.symm '' K) :=
    hK.image_of_continuousOn (e.continuousOn_symm.mono hKe)
  have himage : e.symm '' K ⊆ e.source := by
    rintro _ ⟨z, hz, rfl⟩
    exact e.map_target (hKe hz)
  apply continuous_iff_continuousAt.mpr
  rintro ⟨a, x⟩
  by_cases hx : x ∈ e.source
  · have hcoord : ContinuousAt (fun p : A × M => F p.1 (e p.2)) (a, x) :=
      hF.continuousAt.comp (f := fun p : A × M => (p.1, e p.2))
        (continuous_fst.continuousAt.prodMk
          ((e.continuousAt hx).comp continuous_snd.continuousAt))
    apply ((e.continuousAt_symm (hrange a (e.map_source hx))).comp
      (f := fun p : A × M => F p.1 (e p.2)) hcoord).congr_of_eventuallyEq
    filter_upwards [(e.open_source.preimage continuous_snd).mem_nhds hx] with p hp
    exact chartCorrection_of_mem e (F p.1) hp
  · have hxK : x ∉ e.symm '' K := fun h => hx (himage h)
    apply continuous_snd.continuousAt.congr_of_eventuallyEq
    filter_upwards [(hc.isClosed.isOpen_compl.preimage continuous_snd).mem_nhds hxK] with p hp
    exact chartCorrection_eq_self e (hfix p.1) hp

/-- A supported continuous coordinate self-map preserving the chart
target gives a continuous manifold self-map; Claim 18.22, p. 433. -/
theorem continuous_chartCorrection (e : OpenPartialHomeomorph M E) {f : E → E}
    (hf : Continuous f) {K : Set E} (hK : IsCompact K) (hKe : K ⊆ e.target)
    (hrange : MapsTo f e.target e.target) (hfix : ∀ z ∉ K, f z = z) :
    Continuous (chartCorrection e f) := by
  have hc := continuous_chartCorrection_family (A := Unit) e
    (F := fun _ => f) (hf.comp continuous_snd) hK hKe (fun _ => hrange) (fun _ => hfix)
  exact hc.comp
    ((continuous_const : Continuous (fun _ : M => Unit.unit)).prodMk continuous_id)

/-- The coordinate homotopy glues across the chart boundary because it
is fixed off one compact coordinate set; Claim 18.22, p. 433. -/
noncomputable def chartCorrectionHomotopy (e : OpenPartialHomeomorph M E)
    {f : C(E, E)} (H : (ContinuousMap.id E).Homotopy f)
    {K : Set E} (hK : IsCompact K) (hKe : K ⊆ e.target)
    (hrange : ∀ t : unitInterval, MapsTo (fun z => H (t, z)) e.target e.target)
    (hfix : ∀ (t : unitInterval) z, z ∉ K → H (t, z) = z) :
    (ContinuousMap.id M).Homotopy
      ⟨chartCorrection e f, continuous_chartCorrection e f.continuous hK hKe
        (by intro z hz; simpa only [H.apply_one] using (hrange 1 hz))
        (by intro z hz; simpa only [H.apply_one] using (hfix 1 z hz))⟩ where
  toFun p := chartCorrection e (fun z => H (p.1, z)) p.2
  continuous_toFun := continuous_chartCorrection_family e (F := fun t z => H (t, z))
    H.continuous hK hKe hrange hfix
  map_zero_left x := by
    change chartCorrection e (fun z => H (0, z)) x = x
    by_cases hx : x ∈ e.source
    · rw [chartCorrection_of_mem e _ hx, H.apply_zero]
      exact e.left_inv hx
    · exact chartCorrection_of_not_mem e _ hx
  map_one_left x := by
    change chartCorrection e (fun z => H (1, z)) x = chartCorrection e f x
    congr 1
    funext z
    exact H.apply_one z

end ChartCorrection

section SmoothChartCorrection

variable {M E H : Type*} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] [ChartedSpace H M]
  {J : ModelWithCorners ℝ E H}

/-- A supported smooth coordinate map gives a smooth manifold map. At
the chart boundary it agrees locally with the identity; SurgeryComparison.Transport point
correction, Claim 18.22, p. 433. -/
theorem contMDiff_chartCorrection (e : OpenPartialHomeomorph M E) {f : E → E}
    (hf : ContDiff ℝ ∞ f)
    (he : ContMDiffOn J 𝓘(ℝ, E) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, E) J ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKe : K ⊆ e.target)
    (hrange : MapsTo f e.target e.target) (hfix : ∀ z ∉ K, f z = z) :
    ContMDiff J J ∞ (chartCorrection e f) := by
  intro x
  by_cases hx : x ∈ e.source
  · have he_at := (he x hx).contMDiffAt (e.open_source.mem_nhds hx)
    have hcoord : ContMDiffAt J 𝓘(ℝ, E) ∞
        (fun y => e (id y) + (f (e y) - e y)) x := by
      convert hf.contMDiff.contMDiffAt.comp x he_at using 1
      funext y
      dsimp only [id_eq]
      abel
    apply contMDiffAt_chartPerturb_of_mem e e.open_source hx hcoord hei
    have hsum : e x + (f (e x) - e x) = f (e x) := by abel
    simpa only [id_eq, hsum] using hrange (e.map_source hx)
  · have hxK : x ∉ e.symm '' K := by
      rintro ⟨z, hz, rfl⟩
      exact hx (e.map_target (hKe hz))
    exact contMDiffAt_id.congr_of_eventuallyEq
      (chartCorrection_eventuallyEq e hK hKe hfix hxK)

end SmoothChartCorrection

section RiemannianCoordinates

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

/-- The actual metric norm pulled back by an inverse chart. This avoids
replacing the target metric by a coordinate norm in the SurgeryComparison.Transport correction,
Claim 18.22, p. 433. -/
noncomputable def chartPullbackNorm (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) : ℝ :=
  g.tangentNorm (e.symm p.1) (mfderiv (𝓡 3) (𝓡 3) e.symm p.1 p.2)

/-- Continuity of the tangent map and of the supplied metric gives the
continuous coordinate norm needed by point correction, Claim 18.22,
p. 433. All derivatives are restricted to the open chart target. -/
theorem continuousOn_chartPullbackNorm (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target) :
    ContinuousOn (chartPullbackNorm g e) (e.target ×ˢ univ) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    { exists_continuous := ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩ }
  let V : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) → TangentBundle (𝓡 3) M :=
    fun p => ⟨e.symm p.1, mfderiv (𝓡 3) (𝓡 3) e.symm p.1 p.2⟩
  have hV : ContinuousOn V (e.target ×ˢ univ) := by
    have hT := hei.continuousOn_tangentMapWithin (by simp) e.open_target.uniqueMDiffOn
    have hc := hT.comp
      (tangentBundleModelSpaceHomeomorph (𝓡 3)).symm.continuous.continuousOn
      (s := e.target ×ˢ univ) (fun p hp => hp.1)
    apply hc.congr
    intro p hp
    change (⟨e.symm p.1, mfderiv (𝓡 3) (𝓡 3) e.symm p.1 p.2⟩ : TangentBundle (𝓡 3) M) =
      ⟨e.symm p.1, mfderivWithin (𝓡 3) (𝓡 3) e.symm e.target p.1 p.2⟩
    rw [mfderivWithin_of_isOpen e.open_target hp.1]
  have hi : ContinuousOn
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        g.inner (e.symm p.1) (mfderiv (𝓡 3) (𝓡 3) e.symm p.1 p.2)
          (mfderiv (𝓡 3) (𝓡 3) e.symm p.1 p.2)) (e.target ×ˢ univ) :=
    hV.inner_bundle hV
  exact hi.sqrt

/-- Inverse-chart derivative injectivity makes the pullback norm
positive on nonzero coordinate vectors; Claim 18.22, p. 433. -/
theorem chartPullbackNorm_pos (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (he : e.MDifferentiable (𝓡 3) (𝓡 3))
    {z : EuclideanSpace ℝ (Fin 3)} (hz : z ∈ e.target)
    {w : EuclideanSpace ℝ (Fin 3)} (hw : w ≠ 0) :
    0 < chartPullbackNorm g e (z, w) := by
  apply Real.sqrt_pos.mpr
  apply g.pos
  intro hzero
  apply hw
  change (w : TangentSpace (𝓡 3) z) = 0
  apply he.symm.mfderiv_injective hz
  exact hzero.trans (map_zero (mfderiv (𝓡 3) (𝓡 3) e.symm z)).symm

/-- The actual coordinate norm is absolutely homogeneous, including
at zero; SurgeryComparison.Transport point correction, Claim 18.22, p. 433. -/
theorem chartPullbackNorm_smul (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (z w : EuclideanSpace ℝ (Fin 3)) (c : ℝ) :
    chartPullbackNorm g e (z, c • w) = |c| * chartPullbackNorm g e (z, w) := by
  let D : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    mfderiv (𝓡 3) (𝓡 3) e.symm z
  let B : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
    g.inner (e.symm z)
  change Real.sqrt (B (D (c • w)) (D (c • w))) =
    |c| * Real.sqrt (B (D w) (D w))
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

end RiemannianCoordinates

section RiemannianCorrection

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

/-- Differentiate the literal chart conjugation on the chart source.
This transfers the point-correction estimate to actual tangent vectors,
Claim 18.22, p. 433. -/
theorem mfderiv_chartCorrection
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hf : ContDiff ℝ ∞ f) (he : e.MDifferentiable (𝓡 3) (𝓡 3))
    (hrange : MapsTo f e.target e.target) {x : M} (hx : x ∈ e.source) :
    mfderiv (𝓡 3) (𝓡 3) (chartCorrection e f) x =
      (mfderiv (𝓡 3) (𝓡 3) e.symm (f (e x))).comp
        ((fderiv ℝ f (e x)).comp (mfderiv (𝓡 3) (𝓡 3) e x)) := by
  have heq : chartCorrection e f =ᶠ[𝓝 x] e.symm ∘ (f ∘ e) := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact chartCorrection_of_mem e f hy
  rw [heq.mfderiv_eq]
  have hfm : MDifferentiableAt (𝓡 3) (𝓡 3) f (e x) :=
    hf.contMDiff.mdifferentiableAt (by simp)
  rw [mfderiv_comp x (he.mdifferentiableAt_symm (hrange (e.map_source hx)))
      (hfm.comp x (he.mdifferentiableAt hx)),
    mfderiv_comp x hfm (he.mdifferentiableAt hx), mfderiv_eq_fderiv]
  rfl

/-- A coordinate norm estimate for a supported correction is the exact
quadratic pullback bound for the supplied metric. Off its compact support
the map is locally the identity; Claim 18.22, p. 433. -/
theorem chartCorrection_pullback_le (g : RiemannianMetric 3 M)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hf : ContDiff ℝ ∞ f) (he : e.MDifferentiable (𝓡 3) (𝓡 3))
    {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K) (hKe : K ⊆ e.target)
    (hrange : MapsTo f e.target e.target) (hfix : ∀ z ∉ K, f z = z)
    {C : ℝ} (hC : 1 ≤ C)
    (hbound : ∀ z ∈ e.target, ∀ w,
      chartPullbackNorm g e (f z, fderiv ℝ f z w) ≤ C * chartPullbackNorm g e (z, w)) :
    ∀ x : M, ∀ v : TangentSpace (𝓡 3) x,
      g.inner (chartCorrection e f x) (mfderiv (𝓡 3) (𝓡 3) (chartCorrection e f) x v)
        (mfderiv (𝓡 3) (𝓡 3) (chartCorrection e f) x v) ≤ C ^ 2 * g.inner x v v := by
  -- Fixed model-space types keep point equalities out of the linear-map instances.
  let B : M → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
    fun y => g.inner y
  let D : M → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    fun y => mfderiv (𝓡 3) (𝓡 3) (chartCorrection e f) y
  have hg_nonneg (x : M) (v : EuclideanSpace ℝ (Fin 3)) : 0 ≤ B x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos x v hv).le
  intro x v
  change B (chartCorrection e f x) (D x v) (D x v) ≤ C ^ 2 * B x v v
  by_cases hx : x ∈ e.source
  · have hpoint := chartCorrection_of_mem e f hx
    have hderiv := mfderiv_chartCorrection e hf he hrange hx
    let Dinv : EuclideanSpace ℝ (Fin 3) →
        EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
      fun z => mfderiv (𝓡 3) (𝓡 3) e.symm z
    let w : EuclideanSpace ℝ (Fin 3) := mfderiv (𝓡 3) (𝓡 3) e x v
    have hinv : Dinv (e x) w = v :=
      congrArg (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) => L v)
        (he.symm_comp_deriv hx)
    have hderiv_v : D x v = Dinv (f (e x)) (fderiv ℝ f (e x) w) :=
      congrArg (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) => L v)
        hderiv
    have hb := hbound (e x) (e.map_source hx) w
    change Real.sqrt (B (e.symm (f (e x)))
        (Dinv (f (e x)) (fderiv ℝ f (e x) w))
        (Dinv (f (e x)) (fderiv ℝ f (e x) w))) ≤
      C * Real.sqrt (B (e.symm (e x)) (Dinv (e x) w) (Dinv (e x) w)) at hb
    rw [hinv, e.left_inv hx] at hb
    have hn : Real.sqrt (B (chartCorrection e f x) (D x v) (D x v)) ≤
        C * Real.sqrt (B x v v) := by
      rw [hpoint, hderiv_v]
      exact hb
    have hsquare := mul_self_le_mul_self (Real.sqrt_nonneg _) hn
    simpa only [← pow_two, mul_pow,
      Real.sq_sqrt (hg_nonneg (chartCorrection e f x) (D x v)),
      Real.sq_sqrt (hg_nonneg x v)] using hsquare
  · have hxK : x ∉ e.symm '' K := by
      rintro ⟨z, hz, rfl⟩
      exact hx (e.map_target (hKe hz))
    have heq := chartCorrection_eventuallyEq e hK hKe hfix hxK
    have hpoint : chartCorrection e f x = x := heq.eq_of_nhds
    have heqD : D x =
        (mfderiv (𝓡 3) (𝓡 3) (id : M → M) x :
          EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) := heq.mfderiv_eq
    have hid :
        (mfderiv (𝓡 3) (𝓡 3) (id : M → M) x :
          EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) =
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) := mfderiv_id
    have hderiv : D x = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) :=
      heqD.trans hid
    rw [hpoint, hderiv]
    change B x v v ≤ C ^ 2 * B x v v
    exact le_mul_of_one_le_left (hg_nonneg x v) (by nlinarith)

/-- A nearby point can be moved to a specified point by a smooth map
homotopic to the identity, with arbitrarily small multiplicative loss in
the actual Riemannian distance. The radius is chosen before the nearby
point, as needed for SurgeryComparison.Transport exact-basepoint smoothing, Claim 18.22, p. 433. -/
theorem exists_smooth_pointCorrection [RegularSpace M]
    (g : RiemannianMetric 3 M) (b : M) {η : ℝ} (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧ ∀ a : M, g.edist a b < ENNReal.ofReal r →
      ∃ p : C(M, M), ContMDiff (𝓡 3) (𝓡 3) ∞ p ∧ p a = b ∧
        ContinuousMap.Homotopic p (ContinuousMap.id M) ∧
        ∀ x y : M, g.edist (p x) (p y) ≤ ENNReal.ofReal (1 + η) * g.edist x y := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    { exists_continuous := ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩ }
  let e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)) :=
    chartAt (EuclideanSpace ℝ (Fin 3)) b
  have hbe : b ∈ e.source := mem_chart_source _ _
  have he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source := contMDiffOn_chart
  have hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target := contMDiffOn_chart_symm
  have heM : e.MDifferentiable (𝓡 3) (𝓡 3) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  obtain ⟨ρ, hρ, hcor⟩ := exists_contDiff_pointCorrection_metric e.open_target
    (e.map_source hbe) (chartPullbackNorm g e) (continuousOn_chartPullbackNorm g e hei)
    (fun z hz w hw => chartPullbackNorm_pos g e heM hz hw)
    (fun z _ c w => chartPullbackNorm_smul g e z w c) hη
  have hs : e.source ∩ e ⁻¹' Metric.ball (e b) ρ ∈ 𝓝 b :=
    inter_mem (e.open_source.mem_nhds hbe)
      ((e.continuousAt hbe).preimage_mem_nhds (Metric.ball_mem_nhds _ hρ))
  obtain ⟨r, hr, hrS⟩ := setOfPred_riemannianEDist_lt_subset_nhds (𝓡 3) hs
  refine ⟨(r : ℝ), by exact_mod_cast hr, fun a ha => ?_⟩
  have hba : Manifold.riemannianEDist (𝓡 3) b a < (r : ℝ≥0∞) := by
    change Manifold.riemannianEDist (𝓡 3) a b < ENNReal.ofReal (r : ℝ) at ha
    rw [Manifold.riemannianEDist_comm] at ha
    simpa only [ENNReal.ofReal_coe_nnreal] using ha
  have haS := hrS hba
  obtain ⟨f, hf, hfa, _, _, _, hfbound, H, hH, K, hK, hKe, hfixH⟩ := hcor (e a) haS.2
  have hrange : MapsTo f e.target e.target := by
    intro z hz
    have hh : H (1, z) ∈ e.target := hH 1 hz
    simpa only [H.apply_one] using hh
  have hfix : ∀ z ∉ K, f z = z := by
    intro z hz
    simpa only [H.apply_one] using (hfixH 1 z hz)
  have hp : ContMDiff (𝓡 3) (𝓡 3) ∞ (chartCorrection e f) :=
    contMDiff_chartCorrection e hf he hei hK hKe hrange hfix
  let p : C(M, M) := ⟨chartCorrection e f, hp.continuous⟩
  have hhom : (ContinuousMap.id M).Homotopy p :=
    chartCorrectionHomotopy e H hK hKe hH hfixH
  refine ⟨p, hp, ?_, ⟨hhom.symm⟩, ?_⟩
  · change chartCorrection e f a = b
    rw [chartCorrection_of_mem e f haS.1, hfa, e.left_inv hbe]
  · intro x y
    exact SurgeryComparison.metric_edist_le_mul_of_pullback g g (by linarith) hp
      (chartCorrection_pullback_le g e hf heM hK hKe hrange hfix (by linarith) hfbound) x y

/-- Correct a smooth approximant's basepoint by postcomposition. The
target radius is independent of the approximant and its source basepoint;
the metric factors multiply. This is the exact-point assembly step in
the 2026-09-18 SurgeryComparison.Transport contract, following Claim 18.22, p. 433. -/
theorem exists_smooth_pointCorrected_map [RegularSpace M]
    {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    (g : RiemannianMetric 3 X) (h : RiemannianMetric 3 M)
    (b : M) {η : ℝ} (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧ ∀ (f : C(X, M)), ContMDiff (𝓡 3) (𝓡 3) ∞ f →
      ∀ x₀ : X, h.edist (f x₀) b < ENNReal.ofReal r →
      ∀ C : ℝ, (∀ x y, h.edist (f x) (f y) ≤ ENNReal.ofReal C * g.edist x y) →
      ∃ f' : C(X, M), ContMDiff (𝓡 3) (𝓡 3) ∞ f' ∧ f' x₀ = b ∧
        ContinuousMap.Homotopic f' f ∧
        ∀ x y, h.edist (f' x) (f' y) ≤
          ENNReal.ofReal ((1 + η) * C) * g.edist x y := by
  obtain ⟨r, hr, hcor⟩ := exists_smooth_pointCorrection h b hη
  refine ⟨r, hr, fun f hf x₀ hclose C hbound => ?_⟩
  obtain ⟨p, hp, hpbase, hhom, hpbound⟩ := hcor (f x₀) hclose
  refine ⟨p.comp f, hp.comp hf, hpbase, ?_, ?_⟩
  · simpa only [ContinuousMap.id_comp] using
      hhom.comp (ContinuousMap.Homotopic.refl f)
  · intro x y
    calc
      h.edist (p (f x)) (p (f y)) ≤
          ENNReal.ofReal (1 + η) * h.edist (f x) (f y) := hpbound _ _
      _ ≤ ENNReal.ofReal (1 + η) * (ENNReal.ofReal C * g.edist x y) :=
        mul_le_mul' le_rfl (hbound x y)
      _ = ENNReal.ofReal ((1 + η) * C) * g.edist x y := by
        rw [ENNReal.ofReal_mul (by linarith : 0 ≤ 1 + η), mul_assoc]

/-- Reserve an additive error budget before selecting a smooth map and
then correct its basepoint within the desired final metric factor. This
is the quantitative exact-point step of the 2026-09-18 SurgeryComparison.Transport contract,
following Claim 18.22, p. 433. -/
theorem exists_smooth_pointCorrected_map_with_loss [RegularSpace M]
    {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    (g : RiemannianMetric 3 X) (h : RiemannianMetric 3 M) (b : M)
    {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ loss : ℝ, 0 < loss ∧ ∃ r : ℝ, 0 < r ∧
      ∀ (f : C(X, M)), ContMDiff (𝓡 3) (𝓡 3) ∞ f →
      ∀ x₀ : X, h.edist (f x₀) b < ENNReal.ofReal r →
      (∀ x y, h.edist (f x) (f y) ≤ ENNReal.ofReal (L + loss) * g.edist x y) →
      ∃ f' : C(X, M), ContMDiff (𝓡 3) (𝓡 3) ∞ f' ∧ f' x₀ = b ∧
        ContinuousMap.Homotopic f' f ∧
        ∀ x y, h.edist (f' x) (f' y) ≤ ENNReal.ofReal (L + ε) * g.edist x y := by
  have hden : 0 < L + 2 := by linarith
  let loss : ℝ := min 1 (ε / (L + 2))
  have hloss : 0 < loss := lt_min zero_lt_one (div_pos hε hden)
  have hloss1 : loss ≤ 1 := min_le_left _ _
  have hlosse : loss * (L + 2) ≤ ε :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have hbudget : (1 + loss) * (L + loss) ≤ L + ε := by
    nlinarith [mul_le_of_le_one_right hloss.le hloss1]
  obtain ⟨r, hr, hcor⟩ := exists_smooth_pointCorrected_map g h b hloss
  refine ⟨loss, hloss, r, hr, fun f hf x₀ hclose hbound => ?_⟩
  obtain ⟨f', hf', hbase, hhom, hdist⟩ := hcor f hf x₀ hclose (L + loss) hbound
  refine ⟨f', hf', hbase, hhom, fun x y => (hdist x y).trans ?_⟩
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal hbudget) le_rfl

end RiemannianCorrection


end PoincareMT.SurgeryComparison.Transport
