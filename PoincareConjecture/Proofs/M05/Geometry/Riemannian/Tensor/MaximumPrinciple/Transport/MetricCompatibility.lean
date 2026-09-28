
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.MaximumPrinciple.Transport.Chart
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.MaximumPrinciple.Transport.Jets
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.MaximumPrinciple.Transport.Metric
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Coordinates.Coefficients









noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



lemma chartMetric_eq_inner_constantCoordinateField (p : M) {x : M}
    (hx : x ∈ (extChartAt (𝓡 n) p).source)
    (v w : EuclideanSpace ℝ (Fin n)) :
    g.pullbackCoefficients (extChartAt (𝓡 n) p).symm (extChartAt (𝓡 n) p x) v w =
      g.inner x (constantCoordinateField p v x) (constantCoordinateField p w x) := by
  have hxc : x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source := by simpa using hx
  have hs := TangentBundle.symmL_trivializationAt (I := 𝓡 n) hxc
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hs
  unfold RiemannianMetric.pullbackCoefficients
  simp only [ContinuousLinearMap.bilinearComp_apply, constantCoordinateField, hs]
  congr 2
  congr 1
  exact (extChartAt (𝓡 n) p).left_inv hx



theorem chartMetric_compatibility (D : LeviCivitaData g) (p : M)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ (extChartAt (𝓡 n) p).target)
    (a v w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y => g.pullbackCoefficients (extChartAt (𝓡 n) p).symm y v w) z a =
      g.pullbackCoefficients (extChartAt (𝓡 n) p).symm z
        (D.coordinateConnectionCoefficient p ((extChartAt (𝓡 n) p).symm z) a v) w +
      g.pullbackCoefficients (extChartAt (𝓡 n) p).symm z v
        (D.coordinateConnectionCoefficient p ((extChartAt (𝓡 n) p).symm z) a w) := by
  let c := extChartAt (𝓡 n) p
  let x := c.symm z
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p
  have hx : x ∈ c.source := c.map_target hz
  have hxc : x ∈ e.baseSet := by simpa only [e, TangentBundle.trivializationAt_baseSet,
    c, extChartAt_source] using hx
  let V := constantCoordinateField p v
  let W := constantCoordinateField p w
  let f : M → ℝ := fun y => g.inner y (V y) (W y)
  have hV := contMDiffAt_constantCoordinateField p v hxc
  have hW := contMDiffAt_constantCoordinateField p w hxc
  have hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x := by
    have h := ((g.contMDiff x).clm_bundle_apply hV).clm_bundle_apply hW
    simpa [f, V, W] using (contMDiffAt_totalSpace.mp h).2
  have hcompat := D.mvfderiv_inner_on_fields (constantCoordinateField p a)
    (hV.mdifferentiableAt (by simp)) (hW.mdifferentiableAt (by simp))
  have hdiff := mvfderiv_eq_chart_fderiv p hx
    (hf.mdifferentiableAt (by simp)) (constantCoordinateField p a x)
  have hcoord : e.continuousLinearMapAt ℝ x (constantCoordinateField p a x) = a :=
    e.continuousLinearMapAt_symmL hxc a
  change mvfderiv (𝓡 n) f x (constantCoordinateField p a x) = _ at hcompat
  rw [hdiff, hcoord] at hcompat
  have heq : (f ∘ c.symm) =ᶠ[𝓝 z]
      (fun y => g.pullbackCoefficients c.symm y v w) := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds hz] with y hy
    have h := chartMetric_eq_inner_constantCoordinateField (g := g) p (c.map_target hy) v w
    change g.pullbackCoefficients c.symm (c (c.symm y)) v w = f (c.symm y) at h
    rw [c.right_inv hy] at h
    exact h.symm
  have hcenter : c x = z := c.right_inv hz
  rw [hcenter, heq.fderiv_eq] at hcompat
  rw [hcompat]
  have hv := D.coordinateConnectionCoefficient_apply p hxc a v
  have hw := D.coordinateConnectionCoefficient_apply p hxc a w
  have hlift (b : TangentSpace (𝓡 n) x) :
      constantCoordinateField p (e.continuousLinearMapAt ℝ x b) x = b :=
    e.symmL_continuousLinearMapAt hxc b
  have hmetric (b d : EuclideanSpace ℝ (Fin n)) :
      g.pullbackCoefficients c.symm z b d =
        g.inner x (constantCoordinateField p b x) (constantCoordinateField p d x) := by
    rw [← hcenter]
    exact chartMetric_eq_inner_constantCoordinateField (g := g) p hx b d
  change g.inner x (D.covariantDerivativeOnFields (constantCoordinateField p a) V x) (W x) +
      g.inner x (V x) (D.covariantDerivativeOnFields (constantCoordinateField p a) W x) =
    g.pullbackCoefficients c.symm z (D.coordinateConnectionCoefficient p x a v) w +
      g.pullbackCoefficients c.symm z v (D.coordinateConnectionCoefficient p x a w)
  rw [hmetric, hmetric, hv, hw]
  change _ = g.inner x
    (constantCoordinateField p (e.continuousLinearMapAt ℝ x
      (D.covariantDerivativeOnFields (constantCoordinateField p a) V x)) x) (W x) +
    g.inner x (V x) (constantCoordinateField p (e.continuousLinearMapAt ℝ x
      (D.covariantDerivativeOnFields (constantCoordinateField p a) W x)) x)
  rw [hlift, hlift]


def centeredMetricCoefficients (g : RiemannianMetric n M) (p : M)
    (z : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  g.pullbackCoefficients (extChartAt (𝓡 n) p).symm (extChartAt (𝓡 n) p p + z)

lemma contDiffOn_centeredMetricCoefficients (g : RiemannianMetric n M) (p : M) :
    ContDiffOn ℝ ∞ (centeredMetricCoefficients g p) (centeredChartDomain p) := by
  exact (g.contDiffOn_chartCoefficients p).comp
    (contDiff_const.add contDiff_id).contDiffOn (fun _ hz => hz)


theorem centeredMetric_compatibility (D : LeviCivitaData g) (p : M)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ centeredChartDomain p)
    (a v w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y => centeredMetricCoefficients g p y v w) z a =
      centeredMetricCoefficients g p z (D.centeredConnectionCoefficient p z a v) w +
      centeredMetricCoefficients g p z v (D.centeredConnectionCoefficient p z a w) := by
  let c := extChartAt (𝓡 n) p
  have hB := (g.contDiffOn_chartCoefficients p).contDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds hz)
  have hf := ((hB.clm_apply (contDiffAt_const (c := v))).clm_apply
    (contDiffAt_const (c := w))).differentiableAt (by simp)
  have hd := hf.hasFDerivAt.comp z ((hasFDerivAt_id z).const_add (c p))
  have heq : fderiv ℝ (fun y => g.pullbackCoefficients c.symm (c p + y) v w) z =
      fderiv ℝ (fun y => g.pullbackCoefficients c.symm y v w) (c p + z) := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using hd.fderiv
  change fderiv ℝ (fun y => g.pullbackCoefficients c.symm (c p + y) v w) z a = _
  rw [heq]
  exact D.chartMetric_compatibility p hz a v w

lemma centeredMetric_eq_inner_lift (g : RiemannianMetric n M) (p : M)
    (Y Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    {x : M} (hx : x ∈ (extChartAt (𝓡 n) p).source) :
    centeredMetricCoefficients g p (extChartAt (𝓡 n) p x - extChartAt (𝓡 n) p p)
        (Y (extChartAt (𝓡 n) p x - extChartAt (𝓡 n) p p))
        (Z (extChartAt (𝓡 n) p x - extChartAt (𝓡 n) p p)) =
      g.inner x (fieldFromCenteredCoordinates p Y x) (fieldFromCenteredCoordinates p Z x) := by
  unfold centeredMetricCoefficients fieldFromCenteredCoordinates
  rw [show extChartAt (𝓡 n) p p +
    (extChartAt (𝓡 n) p x - extChartAt (𝓡 n) p p) = extChartAt (𝓡 n) p x by abel]
  exact chartMetric_eq_inner_constantCoordinateField p hx _ _



theorem inner_radialParallelFields (D : LeviCivitaData g) (p : M)
    {r : ℝ} (hr : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r ⊆ centeredChartDomain p)
    (Y Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hY : ∀ u ∈ Metric.ball 0 r, ∀ t ∈ Icc (-1 : ℝ) 1,
      HasDerivAt (fun s : ℝ => Y (s • u))
        (-(D.centeredConnectionCoefficient p (t • u) u (Y (t • u)))) t)
    (hZ : ∀ u ∈ Metric.ball 0 r, ∀ t ∈ Icc (-1 : ℝ) 1,
      HasDerivAt (fun s : ℝ => Z (s • u))
        (-(D.centeredConnectionCoefficient p (t • u) u (Z (t • u)))) t)
    {x : M} (hx : x ∈ (extChartAt (𝓡 n) p).source)
    (hxr : extChartAt (𝓡 n) p x - extChartAt (𝓡 n) p p ∈ Metric.ball 0 r) :
    g.inner x (fieldFromCenteredCoordinates p Y x) (fieldFromCenteredCoordinates p Z x) =
      g.inner p (fieldFromCenteredCoordinates p Y p) (fieldFromCenteredCoordinates p Z p) := by
  let u := extChartAt (𝓡 n) p x - extChartAt (𝓡 n) p p
  have hsegment (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      t • u ∈ centeredChartDomain p := by
    apply hr
    rw [Metric.mem_ball, dist_zero_right] at hxr ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg u) ht.2).trans_lt hxr
  have ht (t : ℝ) (h : t ∈ Icc (0 : ℝ) 1) : t ∈ Icc (-1 : ℝ) 1 :=
    ⟨by linarith [h.1], h.2⟩
  have h := Poincare.Riemannian.RadialTransport.fields_metric_eq_of_radial_parallel
    (isOpen_centeredChartDomain p)
    ((contDiffOn_centeredMetricCoefficients g p).differentiableOn (by simp))
    (fun z hz a v w => D.centeredMetric_compatibility p hz a v w) u hsegment Y Z
    (fun t h => hY u hxr t (ht t h)) (fun t h => hZ u hxr t (ht t h))
  rw [centeredMetric_eq_inner_lift g p Y Z hx] at h
  have hzero := centeredMetric_eq_inner_lift g p Y Z (mem_extChartAt_source p)
  simp only [sub_self] at hzero
  exact h.trans hzero

end PoincareConjecture.LeviCivitaData
