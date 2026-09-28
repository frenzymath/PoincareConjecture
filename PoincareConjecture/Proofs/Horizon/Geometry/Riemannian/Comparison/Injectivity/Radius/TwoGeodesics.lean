import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.Radius.Exponential
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.BallDiffeomorphism
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.TwoBranches
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Polar.NoBranching
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.ReturnedLoop

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem edist_globalExponential_eq_tangentNorm_of_lt_truncatedInjectivityRadius
    (g : RiemannianMetric n M) (hc : MetricComplete g) {C : ℝ}
    (hC : 0 ≤ C) (p : M) {v : EuclideanSpace ℝ (Fin n)}
    (hv : g.tangentNorm p v < g.truncatedInjectivityRadius hc C p) :
    g.edist p (g.globalExponential hc p v) = ENNReal.ofReal (g.tangentNorm p v) := by
  let R := C + 1
  have hR : 0 < R := by dsimp [R]; linarith
  have hρR : g.truncatedInjectivityRadius hc C p ≤ R :=
    (g.truncatedInjectivityRadius_le hc hC p).trans (by dsimp [R]; linarith)
  obtain ⟨L, e, hL, _, he0, hed, hgeo⟩ :=
    g.exists_orthonormal_radial_exponential_of_metricComplete hc p hR
  have hnorm : g.tangentNorm p v = ‖L.symm v‖ := by
    simpa using g.tangentNorm_orthonormal_frame p L hL (L.symm v)
  have hvρ : L.symm v ∈ Metric.ball 0 (g.truncatedInjectivityRadius hc C p) := by
    simpa [hnorm] using hv
  have hρ : 0 < g.truncatedInjectivityRadius hc C p := (Real.sqrt_nonneg _).trans_lt hv
  have hcover := Poincare.VolumeComparison.image_localMinimizingSet_eq_ball g p hR
    (g.isCompact_closure_ball_of_metricComplete hc p R) L e hL he0 hed
    (fun w hw => (hgeo w hw).1)
  have hmin := (g.image_ball_and_radial_edist_eq_of_injOn p hρ hρR hcover
    (fun w hw => by
      have h := ((hgeo w (Metric.ball_subset_ball hρR hw)).2 1 (by simp)).2
      simpa using h)
    (g.injOn_radial_exponential_of_le_truncatedInjectivityRadius hc p hR hC hρR
      le_rfl L e hL he0 hed (fun w hw => (hgeo w hw).1))).2 (L.symm v) hvρ
  have heq := g.globalExponential_eq_radial_exponential hc p hR L e he0 hed
    (fun w hw => (hgeo w hw).1) (Metric.ball_subset_ball hρR hvρ)
  simp only [L.apply_symm_apply] at heq
  rw [heq, hnorm]
  exact hmin

omit [T3Space M] in
private theorem tangentNorm_smul (g : RiemannianMetric n M) (p : M)
    (t : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    g.tangentNorm p (t • v) = |t| * g.tangentNorm p v := by
  simp only [tangentNorm, map_smul, smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs]

theorem globalExponential_smul_eq_globalGeodesic
    (g : RiemannianMetric n M) (hc : MetricComplete g) (p : M)
    (v : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    g.globalExponential hc p (t • v) = g.globalGeodesic hc p v t := by
  obtain ⟨hgeo, hp, hd⟩ := g.globalGeodesic_spec hc p v
  have hscale : g.IsGeodesicOn (fun s => g.globalGeodesic hc p v (t * s))
      (Icc (0 : ℝ) 1) := fun s _ => hgeo.comp_mul t s (mem_univ _)
  have hds : HasDerivAt (fun s => extChartAt (𝓡 n) p
      (g.globalGeodesic hc p v (t * s))) (t • v) 0 := by
    have hd' : HasDerivAt (fun s => extChartAt (𝓡 n) p
        (g.globalGeodesic hc p v s)) v (t * 0) := by simpa using hd
    simpa only [Function.comp_def, id_eq, mul_one] using
      hd'.scomp 0 ((hasDerivAt_id (0 : ℝ)).const_mul t)
  simpa only [mul_one] using g.globalExponential_eq_endpoint hc p (t • v)
    hscale (by simpa using hp) hds

theorem edist_globalGeodesic_le_tangentNorm
    (g : RiemannianMetric n M) (hc : MetricComplete g) (p : M)
    (v : EuclideanSpace ℝ (Fin n)) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    g.edist (g.globalGeodesic hc p v s) (g.globalGeodesic hc p v t) ≤
      ENNReal.ofReal (|s - t| * g.tangentNorm p v) := by
  obtain ⟨hgeo, hp, hd⟩ := g.globalGeodesic_spec hc p v
  have hgeo' : g.IsGeodesicOn (g.globalGeodesic hc p v) (Icc (0 : ℝ) 1) :=
    fun u _ => hgeo u (mem_univ u)
  apply Poincare.VolumeComparison.edist_le_of_geodesic_speed_Icc g hgeo' _ hs ht
  intro u hu
  exact (Poincare.VolumeComparison.tangentNorm_eq_of_mem_Icc g hgeo' hu
    (by simp : (0 : ℝ) ∈ Icc 0 1)).trans
    (Poincare.VolumeComparison.tangentNorm_coordDeriv_eq g hgeo' (by simp) hp hd).symm

private theorem truncatedInjectivityRadius_le_average_of_shorter_collision
    (g : RiemannianMetric n M) (hc : MetricComplete g) {C : ℝ}
    (hC : 0 ≤ C) (p : M) {v w : EuclideanSpace ℝ (Fin n)}
    (heq : g.globalExponential hc p v = g.globalExponential hc p w)
    (hlt : g.tangentNorm p w < g.tangentNorm p v) :
    g.truncatedInjectivityRadius hc C p ≤ (g.tangentNorm p v + g.tangentNorm p w) / 2 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let a := g.tangentNorm p v
  let b := g.tangentNorm p w
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have ha : 0 < a := hb.trans_lt hlt
  by_contra hnot
  have hmr : (a + b) / 2 < g.truncatedInjectivityRadius hc C p := lt_of_not_ge hnot
  have hma : (a + b) / 2 < a := by linarith
  obtain ⟨s, hms, hs⟩ := exists_between (lt_min hma hmr)
  have hsa : s < a := hs.trans_le (min_le_left _ _)
  have hsr : s < g.truncatedInjectivityRadius hc C p := hs.trans_le (min_le_right _ _)
  have hspos : 0 < s := by linarith
  have ht : s / a ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hspos.le ha.le, (div_le_one ha).mpr hsa.le⟩
  have hnorm : g.tangentNorm p ((s / a) • v) = s := by
    rw [tangentNorm_smul, abs_of_nonneg ht.1]
    change s / a * a = s
    exact div_mul_cancel₀ s ha.ne'
  have hmin := g.edist_globalExponential_eq_tangentNorm_of_lt_truncatedInjectivityRadius
    hc hC p (by rw [hnorm]; exact hsr)
  rw [g.globalExponential_smul_eq_globalGeodesic, hnorm] at hmin
  have hshort := g.edist_globalGeodesic_le_tangentNorm hc p w
    (by simp : (0 : ℝ) ∈ Icc 0 1) (by simp : (1 : ℝ) ∈ Icc 0 1)
  have hshort' : g.edist p (g.globalExponential hc p v) ≤ ENNReal.ofReal b := by
    rw [heq]
    simpa only [globalExponential, (g.globalGeodesic_spec hc p w).2.1,
      sub_zero, zero_sub, abs_neg, abs_one, one_mul] using hshort
  have htail := g.edist_globalGeodesic_le_tangentNorm hc p v
    (by simp : (1 : ℝ) ∈ Icc 0 1) ht
  have htail' : g.edist (g.globalExponential hc p v) (g.globalGeodesic hc p v (s / a)) ≤
      ENNReal.ofReal (a - s) := by
    have halg : |1 - s / a| * a = a - s := by
      rw [abs_of_nonneg (sub_nonneg.mpr ht.2)]
      field_simp
    change g.edist (g.globalExponential hc p v) (g.globalGeodesic hc p v (s / a)) ≤
      ENNReal.ofReal (|1 - s / a| * a) at htail
    rw [halg] at htail
    exact htail
  have htriangle : g.edist p (g.globalGeodesic hc p v (s / a)) ≤
      ENNReal.ofReal b + ENNReal.ofReal (a - s) :=
    (edist_triangle p (g.globalExponential hc p v)
      (g.globalGeodesic hc p v (s / a))).trans (add_le_add hshort' htail')
  rw [hmin, ← ENNReal.ofReal_add hb (sub_nonneg.mpr hsa.le)] at htriangle
  have hsle : s ≤ b + (a - s) :=
    (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp htriangle
  linarith

theorem truncatedInjectivityRadius_le_average_of_collision
    (g : RiemannianMetric n M) (hc : MetricComplete g) {C : ℝ}
    (hC : 0 ≤ C) (p : M) {v w : EuclideanSpace ℝ (Fin n)}
    (hne : v ≠ w) (heq : g.globalExponential hc p v = g.globalExponential hc p w) :
    g.truncatedInjectivityRadius hc C p ≤ (g.tangentNorm p v + g.tangentNorm p w) / 2 := by
  rcases lt_trichotomy (g.tangentNorm p v) (g.tangentNorm p w) with hlt | he | hgt
  · have h := g.truncatedInjectivityRadius_le_average_of_shorter_collision hc hC p heq.symm hlt
    simpa only [add_comm] using h
  · have h := g.truncatedInjectivityRadius_le_max_of_collision hc hC p hne heq
    rw [he, max_self] at h
    linarith
  · exact g.truncatedInjectivityRadius_le_average_of_shorter_collision hc hC p heq hgt

theorem truncatedInjectivityRadius_le_average_of_radial_collision
    (g : RiemannianMetric n M) (hc : MetricComplete g) {C R : ℝ}
    (hC : 0 ≤ C) (p : M)
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (e : EuclideanSpace ℝ (Fin n) → M) (he0 : e 0 = p)
    (hed : HasFDerivAt (fun v => extChartAt (𝓡 n) p (e v)) L.toContinuousLinearMap 0)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    (hgeo : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun t : ℝ => e (t • v)) {t : ℝ | t • v ∈ Metric.ball 0 R})
    (hgauss : ∀ z ∈ Metric.ball 0 R, ∀ a : EuclideanSpace ℝ (Fin n),
      g.inner (e z) (mfderiv (𝓡 n) (𝓡 n) e z z)
        (mfderiv (𝓡 n) (𝓡 n) e z a) = inner ℝ z a)
    {v w : EuclideanSpace ℝ (Fin n)}
    (hv : v ∈ Metric.ball 0 R) (hw : w ∈ Metric.ball 0 R)
    (hne : v ≠ w) (heq : e v = e w) :
    g.truncatedInjectivityRadius hc C (e v) ≤ (‖v‖ + ‖w‖) / 2 := by
  have hsegment (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ Metric.ball 0 R) :
      g.IsGeodesicOn (fun t : ℝ => e (t • z)) (Icc (0 : ℝ) 1) := by
    intro t ht
    apply hgeo z hz t
    simp only [mem_ofPred_eq, Metric.mem_ball, dist_zero_right] at hz ⊢
    rw [norm_smul, Real.norm_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg z)).trans_lt (by simpa using hz)
  have hterminal (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ Metric.ball 0 R) :
      HasDerivAt (fun t : ℝ => extChartAt (𝓡 n) (e z) (e (t • z)))
        (mfderiv (𝓡 n) (𝓡 n) e z z) 1 := by
    have hd := hasFDerivAt_endpoint_chart
      ((he.contMDiffAt (Metric.isOpen_ball.mem_nhds hz)).mdifferentiableAt (by simp))
    have hd' : HasFDerivAt (fun x => extChartAt (𝓡 n) (e z) (e x))
        (show EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) from
          mfderiv (𝓡 n) (𝓡 n) e z) ((1 : ℝ) • z) := by simpa using hd
    simpa only [Function.comp_def, id_eq, one_smul] using!
      hd'.comp_hasDerivAt 1 ((hasDerivAt_id (1 : ℝ)).smul_const z)
  have hinitial (z : EuclideanSpace ℝ (Fin n)) :
      HasDerivAt (fun t : ℝ => extChartAt (𝓡 n) p (e (t • z))) (L z) 0 := by
    simpa only [Function.comp_def, ContinuousLinearEquiv.coe_coe, one_smul, id_eq] using
      hed.comp_hasDerivAt_of_eq 0 ((hasDerivAt_id (0 : ℝ)).smul_const z) (by simp)
  have hterminalne : mfderiv (𝓡 n) (𝓡 n) e v v ≠ mfderiv (𝓡 n) (𝓡 n) e w w := by
    intro hvel
    have htw : HasDerivAt (fun t : ℝ => extChartAt (𝓡 n) (e v) (e (t • w)))
        (mfderiv (𝓡 n) (𝓡 n) e w w) 1 := by rw [heq]; exact hterminal w hw
    have hgerm := (hsegment v hv).eq_nhds_on_of_initial_data (hsegment w hw)
      (convex_Icc (0 : ℝ) 1).isPreconnected (t₀ := 1) (by simp) (e v)
      (by simp)
      (by simpa using heq) ((hterminal v hv).deriv.trans (hvel.trans htw.deriv.symm))
    have hder := ((hgerm 0 (by simp)).fun_comp (extChartAt (𝓡 n) p)).deriv_eq
    simp only [Function.comp_def] at hder
    rw [(hinitial v).deriv, (hinitial w).deriv] at hder
    exact hne (L.injective hder)
  have hreverse (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ Metric.ball 0 R) :
      g.globalExponential hc (e z) (-mfderiv (𝓡 n) (𝓡 n) e z z) = p := by
    have hrev : g.IsGeodesicOn (fun t : ℝ => e ((-1 * t + 1) • z))
        (Icc (0 : ℝ) 1) := by
      intro t ht
      apply (hsegment z hz).comp_affine (-1) 1 t
      change -1 * t + 1 ∈ Icc (0 : ℝ) 1
      constructor <;> linarith [ht.1, ht.2]
    have hd := hasFDerivAt_endpoint_chart
      ((he.contMDiffAt (Metric.isOpen_ball.mem_nhds hz)).mdifferentiableAt (by simp))
    have hd' : HasFDerivAt (fun x => extChartAt (𝓡 n) (e z) (e x))
        (show EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) from
          mfderiv (𝓡 n) (𝓡 n) e z) ((-(1 : ℝ) * 0 + 1) • z) := by simpa using hd
    have hs : HasDerivAt (fun t : ℝ => (-1 * t + 1) • z) (-z) 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).const_mul (-1)).add_const 1).smul_const z
    have hrevder : HasDerivAt (fun t : ℝ => extChartAt (𝓡 n) (e z)
        (e ((-1 * t + 1) • z))) (-mfderiv (𝓡 n) (𝓡 n) e z z) 0 := by
      simpa only [Function.comp_def, map_neg] using! hd'.comp_hasDerivAt 0 hs
    have h := g.globalExponential_eq_endpoint hc (e z)
      (-mfderiv (𝓡 n) (𝓡 n) e z z) hrev (by simp) hrevder
    simpa [he0] using h
  have hcollision :
      g.globalExponential hc (e v) (-mfderiv (𝓡 n) (𝓡 n) e v v) =
        g.globalExponential hc (e v) (-mfderiv (𝓡 n) (𝓡 n) e w w) := by
    have hwrev : g.globalExponential hc (e v) (-mfderiv (𝓡 n) (𝓡 n) e w w) = p := by
      rw [heq]
      exact hreverse w hw
    exact (hreverse v hv).trans hwrev.symm
  have hnorm (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ Metric.ball 0 R) :
      g.tangentNorm (e z) (-mfderiv (𝓡 n) (𝓡 n) e z z) = ‖z‖ := by
    simp only [tangentNorm, map_neg, neg_apply, neg_neg, hgauss z hz z,
      real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg z)]
  have h := g.truncatedInjectivityRadius_le_average_of_collision hc hC (e v)
    (fun h => hterminalne (neg_injective h)) hcollision
  rw [hnorm v hv] at h
  have hnormw : g.tangentNorm (e v) (-mfderiv (𝓡 n) (𝓡 n) e w w) = ‖w‖ := by
    rw [heq]
    exact hnorm w hw
  rwa [hnormw] at h

end PoincareConjecture.RiemannianMetric
