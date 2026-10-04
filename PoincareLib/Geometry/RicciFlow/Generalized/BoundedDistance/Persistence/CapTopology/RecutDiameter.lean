import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Persistence.CapTopology.RecutVolume
import PoincareLib.Geometry.Riemannian.MetricComparison

/-!
# Actual differential control of recut diameter

Morgan--Tian Proposition 9.79, pp. 232-234. A differential norm bound on
an actual partial diffeomorphism controls transported path lengths and
the frozen intrinsic diameter. For an old-metric cap recut this produces
the diameter margin with explicit slack. See the task derivation
`cap-topology/2026-09-23-recut-quantitative-producers.md`.
-/

set_option autoImplicit false

open Set Function MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u v

namespace PoincareMT.CapRecut

variable {M : Type u} {M' : Type v} [TopologicalSpace M] [TopologicalSpace M']
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M']
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ M']

/-- The actual differential bound of a partial diffeomorphism controls
the length of each C1 source path. Endpoints are handled by the
Lebesgue-null difference between the open and closed parameter intervals. -/
theorem pathELength_comp_le_of_differential_bound
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 M')
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M M' ∞)
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ x ∈ e.source, ∀ w : TangentSpace (𝓡 3) x,
      h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x w) ≤
        L * g.tangentNorm x w)
    {γ : ℝ → M} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc 0 1))
    (himage : γ '' Icc 0 1 ⊆ e.source) :
    h.pathELength (e ∘ γ) 0 1 ≤ ENNReal.ofReal L * g.pathELength γ 0 1 := by
  rw [RiemannianMetric.pathELength_eq_lintegral_tangentNorm,
    RiemannianMetric.pathELength_eq_lintegral_tangentNorm,
    ← restrict_Ioo_eq_restrict_Icc,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' measurableSet_Ioo
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have hx : γ t ∈ e.source := himage ⟨t, ht', rfl⟩
  have he := (e.contMDiffOn_toFun.contMDiffAt
    (e.open_source.mem_nhds hx)).mdifferentiableAt (by simp)
  have hg := (hγ.contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt
    one_ne_zero
  rw [mfderiv_comp t he hg, ContinuousLinearMap.comp_apply]
  exact (ENNReal.ofReal_le_ofReal (hbound (γ t) hx _)).trans_eq
    (ENNReal.ofReal_mul hL)

/-- Infimizing transported C1 paths gives a bound for the actual frozen
intrinsic distance. This requires no ambient completeness or minimizing
path and remains valid when the source distance is infinite. -/
theorem intrinsicEDist_le_mul_of_differential_bound
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 M')
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M M' ∞)
    {L : ℝ} (hL : 0 < L)
    (hbound : ∀ x ∈ e.source, ∀ w : TangentSpace (𝓡 3) x,
      h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x w) ≤
        L * g.tangentNorm x w)
    (x y : M) :
    intrinsicEDist h e.target (e x) (e y) ≤
      ENNReal.ofReal L * intrinsicEDist g e.source x y := by
  have hLzero : ENNReal.ofReal L ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hL)
  have hdiv : intrinsicEDist h e.target (e x) (e y) / ENNReal.ofReal L ≤
      intrinsicEDist g e.source x y := by
    apply le_sInf
    rintro _ ⟨γ, hγ, hγ0, hγ1, himage, rfl⟩
    apply (ENNReal.div_le_iff hLzero ENNReal.ofReal_ne_top).mpr
    rw [mul_comm _ (ENNReal.ofReal L)]
    have hsmooth : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (e ∘ γ) (Icc 0 1) :=
      (e.contMDiffOn_toFun.of_le (by simp)).comp hγ
        (fun t ht => himage ⟨t, ht, rfl⟩)
    have htarget : (e ∘ γ) '' Icc 0 1 ⊆ e.target := by
      rintro _ ⟨t, ht, rfl⟩
      exact e.map_source (himage ⟨t, ht, rfl⟩)
    have hd : intrinsicEDist h e.target (e x) (e y) ≤
        h.pathELength (e ∘ γ) 0 1 :=
      sInf_le ⟨e ∘ γ, hsmooth, by simp [hγ0], by simp [hγ1], htarget, rfl⟩
    exact hd.trans (pathELength_comp_le_of_differential_bound
      g h e hL.le hbound hγ himage)
  simpa only [mul_comm] using
    (ENNReal.div_le_iff hLzero ENNReal.ofReal_ne_top).mp hdiv

/-- The actual intrinsic diameter of a partial diffeomorphism's target
is controlled by its source diameter and its tangent-norm distortion.
Source and target metrics and carrier universes may differ. -/
theorem intrinsicDiameter_le_mul_of_differential_bound
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 M')
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M M' ∞)
    {L : ℝ} (hL : 0 < L)
    (hbound : ∀ x ∈ e.source, ∀ w : TangentSpace (𝓡 3) x,
      h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x w) ≤
        L * g.tangentNorm x w) :
    intrinsicDiameter h e.target ≤ ENNReal.ofReal L * intrinsicDiameter g e.source := by
  apply sSup_le
  rintro _ ⟨⟨x, y⟩, rfl⟩
  have hd := intrinsicEDist_le_mul_of_differential_bound
    g h e hL hbound (e.symm x) (e.symm y)
  have hxinv : e (e.symm.toPartialEquiv x) = x := e.right_inv x.2
  have hyinv : e (e.symm.toPartialEquiv y) = y := e.right_inv y.2
  rw [hxinv, hyinv] at hd
  apply hd.trans
  apply mul_le_mul' le_rfl
  exact le_sSup ⟨(⟨e.symm x, e.map_target x.2⟩,
    ⟨e.symm y, e.map_target y.2⟩), rfl⟩

end PoincareMT.CapRecut

namespace PoincareMT.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] {g : RiemannianMetric 3 M}

/-- Actual differential control of a cap compression supplies its strict
diameter margin. The factor `L` consumes at most the explicit one-unit
enlargement of the old cap constant. -/
theorem recut_diameter_bound_of_differential_bound
    (N : CapCertificate g)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M M ∞)
    (hsource : e.source = N.carrier) (htarget : e.target ⊆ N.carrier)
    {L : ℝ} (hL : 0 < L) (hslack : L * N.cap_constant ≤ N.cap_constant + 1)
    (hbound : ∀ x ∈ e.source, ∀ w : TangentSpace (𝓡 3) x,
      g.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x w) ≤
        L * g.tangentNorm x w) :
    intrinsicDiameter g e.target < ENNReal.ofReal ((N.cap_constant + 1) *
      scalarCurvatureSupOn g N.connection e.target ^ (-1 / 2 : ℝ)) := by
  obtain ⟨x, hx⟩ := N.core_nonempty
  have hxN : x ∈ N.carrier := by
    have hxY := interior_subset (N.core_eq_interior_closed_core ▸ hx)
    exact (N.closed_core_eq_complement_end ▸ hxY).1
  have hne : e.target.Nonempty := ⟨e x, e.map_source (hsource.symm ▸ hxN)⟩
  obtain ⟨hpos, hsup⟩ := N.scalar_sup_pos_and_le_of_subset hne htarget
  have hpower := Real.rpow_le_rpow_of_nonpos hpos hsup
    (show (-1 / 2 : ℝ) ≤ 0 by norm_num)
  have hd := CapRecut.intrinsicDiameter_le_mul_of_differential_bound g g e hL hbound
  rw [hsource] at hd
  apply (hd.trans_lt (ENNReal.mul_lt_mul_right
    (ne_of_gt (ENNReal.ofReal_pos.mpr hL)) ENNReal.ofReal_ne_top
      N.intrinsic_diameter_bound)).trans_le
  rw [← ENNReal.ofReal_mul hL.le]
  apply ENNReal.ofReal_le_ofReal
  calc
    L * (N.cap_constant *
        scalarCurvatureSupOn g N.connection N.carrier ^ (-1 / 2 : ℝ)) =
      (L * N.cap_constant) *
        scalarCurvatureSupOn g N.connection N.carrier ^ (-1 / 2 : ℝ) := by ring
    _ ≤ (N.cap_constant + 1) *
        scalarCurvatureSupOn g N.connection e.target ^ (-1 / 2 : ℝ) := by
      exact mul_le_mul hslack hpower (Real.rpow_nonneg (hpos.le.trans hsup) _)
        (by linarith [N.cap_constant_pos])

/-- From an actual cap compression, first-derivative distortion and
uniform old-core-ball confinement produce all inherited recut margins.
Neither target diameter nor target volume is an input. -/
theorem exists_quantitative_cap_recut_margins_of_differential_bound
    (N : CapCertificate g)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M M ∞)
    (hsource : e.source = N.carrier) (htarget : e.target ⊆ N.carrier)
    {L : ℝ} (hL : 0 < L) (hslack : L * N.cap_constant ≤ N.cap_constant + 1)
    (hbound : ∀ x ∈ e.source, ∀ w : TangentSpace (𝓡 3) x,
      g.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x w) ≤
        L * g.tangentNorm x w)
    (hball : ∀ y ∈ N.core,
      closure (g.ball y (N.core_radius y)) ⊆ e.target) :
    Nonempty (QuantitativeCapRecutMargins N e.target) := by
  obtain ⟨x, hx⟩ := N.core_nonempty
  have hxN : x ∈ N.carrier := by
    have hxY := interior_subset (N.core_eq_interior_closed_core ▸ hx)
    exact (N.closed_core_eq_complement_end ▸ hxY).1
  exact N.exists_quantitative_cap_recut_margins_of_diameter_and_core_balls
    ⟨e x, e.map_source (hsource.symm ▸ hxN)⟩ htarget
    (N.recut_diameter_bound_of_differential_bound e hsource htarget hL hslack hbound)
    hball

end PoincareMT.CapCertificate
