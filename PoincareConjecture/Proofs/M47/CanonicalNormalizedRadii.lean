import PoincareConjecture.Proofs.M47.CanonicalScalarStability
import PoincareConjecture.Proofs.M47.CanonicalMetricStability
import PoincareConjecture.Proofs.M34.Lemma12_3_Estimates.Regularity

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M]

theorem scalar_normalized_radius_le_of_close
    (g h : RiemannianMetric 3 M) (Dg : LeviCivitaData g) (Dh : LeviCivitaData h)
    (x : M) {r s A c m eta : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hnormalg : scalarCurvatureSupOn g Dg (g.ball x r) = r⁻¹ ^ 2)
    (hnormalh : scalarCurvatureSupOn h Dh (h.ball x s) = s⁻¹ ^ 2)
    (hA : 1 ≤ A) (hc : 1 < c) (_hm : 0 < m)
    (hcenter : m ≤ Dg.scalarCurvature x)
    (hdist : ∀ y : M, h.edist x y ≤ ENNReal.ofReal A * g.edist x y)
    (hscalar : ∀ y : M, Dg.scalarCurvature y ≤ Dh.scalarCurvature y + eta)
    (heta : eta ≤ m * (1 - c⁻¹ ^ 2)) :
    s ≤ A * c * r := by
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hcpos : 0 < c := zero_lt_one.trans hc
  have hcinv : 0 < c⁻¹ := inv_pos.mpr hcpos
  have hcinvone : c⁻¹ < 1 := (inv_lt_one₀ hcpos).mpr hc
  have hfactor : 0 < 1 - c⁻¹ ^ 2 := by nlinarith
  have hx : x ∈ g.ball x r := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change Manifold.riemannianEDist (𝓡 3) x x < ENNReal.ofReal r
    rw [Manifold.riemannianEDist_self]
    exact ENNReal.ofReal_pos.mpr hr
  have hb (D : LeviCivitaData g) : BddAbove (D.scalarCurvature '' g.ball x r) :=
    (isCompact_univ.bddAbove_image (M34.contMDiff_scalarCurvature D).continuous.continuousOn).mono
      (image_mono (subset_univ _))
  have hbnew : BddAbove (Dh.scalarCurvature '' h.ball x s) :=
    (isCompact_univ.bddAbove_image (M34.contMDiff_scalarCurvature Dh).continuous.continuousOn).mono
      (image_mono (subset_univ _))
  have hfloor : m ≤ r⁻¹ ^ 2 := by
    have h := hcenter.trans (le_csSup (hb Dg) (mem_image_of_mem Dg.scalarCurvature hx))
    simpa only [← hnormalg, scalarCurvatureSupOn, image_eq_range] using h
  by_contra hnot
  have hlarge : A * c * r < s := lt_of_not_ge hnot
  have hAr : A * r < s := by
    have h := mul_lt_mul_of_pos_left hc (mul_pos hApos hr)
    nlinarith
  have hballs : g.ball x r ⊆ h.ball x s := by
    intro y hy
    have hle : h.edist x y ≤ ENNReal.ofReal (A * r) :=
      (hdist y).trans (by
        rw [ENNReal.ofReal_mul hApos.le]
        exact mul_le_mul' le_rfl (show g.edist x y ≤ ENNReal.ofReal r from hy.le))
    exact hle.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hs).mpr hAr)
  have hsup : r⁻¹ ^ 2 ≤ s⁻¹ ^ 2 + eta := by
    rw [← hnormalg, scalarCurvatureSupOn, ← image_eq_range]
    apply csSup_le ⟨Dg.scalarCurvature x, mem_image_of_mem Dg.scalarCurvature hx⟩
    rintro _ ⟨y, hy, rfl⟩
    have hnew := le_csSup hbnew (mem_image_of_mem Dh.scalarCurvature (hballs hy))
    have hnew' : Dh.scalarCurvature y ≤ s⁻¹ ^ 2 := by
      simpa only [← hnormalh, scalarCurvatureSupOn, image_eq_range] using hnew
    exact (hscalar y).trans (add_le_add hnew' le_rfl)
  have herror : eta ≤ r⁻¹ ^ 2 * (1 - c⁻¹ ^ 2) :=
    heta.trans (mul_le_mul_of_nonneg_right hfloor hfactor.le)
  have hsq : ((c * r)⁻¹) ^ 2 ≤ (s⁻¹) ^ 2 := by
    rw [mul_inv, mul_pow]
    nlinarith
  have hinv := (sq_le_sq₀ (inv_nonneg.mpr (mul_pos hcpos hr).le)
    (inv_nonneg.mpr hs.le)).mp hsq
  have hshort : s ≤ c * r := (inv_le_inv₀ (mul_pos hcpos hr) hs).mp hinv
  have hAcr : c * r ≤ A * c * r := by
    simpa only [one_mul, mul_assoc] using
      mul_le_mul_of_nonneg_right hA (mul_pos hcpos hr).le
  exact hlarge.not_ge (hshort.trans hAcr)

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]

theorem cap_normalized_radii_close
    (hC : RicciFlowCurvatureTheory.{u}) {a b : ℝ} (F : RicciFlow 3 M (Icc a b))
    (t : Icc a b) (N : CapCertificate (F.metric t.val))
    (hconnection : N.connection = F.connection t.val) {Lambda : ℝ} (hLambda : 1 < Lambda) :
    ∀ᶠ s : Icc a b in 𝓝 t, ∀ y ∈ N.core, ∀ r : ℝ, 0 < r →
      scalarCurvatureSupOn (F.metric s.val) (F.connection s.val)
        ((F.metric s.val).ball y r) = r⁻¹ ^ 2 →
      r ≤ Lambda * N.core_radius y ∧ N.core_radius y ≤ Lambda * r := by
  obtain ⟨m, hm, _, _, _, hlower, _⟩ := cap_uniform_scalar_lower N
  rw [hconnection] at hlower
  let c := Real.sqrt Lambda
  have hc : 1 < c := by
    apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).mpr
    simpa only [one_pow] using hLambda
  have hcpos : 0 < c := zero_lt_one.trans hc
  have hcc : c * c = Lambda := by
    simpa only [← pow_two] using Real.sq_sqrt (zero_lt_one.trans hLambda).le
  have hcinv : 0 < c⁻¹ := inv_pos.mpr hcpos
  have hcinvone : c⁻¹ < 1 := (inv_lt_one₀ hcpos).mpr hc
  have hfactor : 0 < 1 - c⁻¹ ^ 2 := by nlinarith
  let eta := min (m / 2) ((m / 2) * (1 - c⁻¹ ^ 2))
  have heta : 0 < eta := lt_min (half_pos hm) (mul_pos (half_pos hm) hfactor)
  have hetam : eta ≤ m / 2 := min_le_left _ _
  have hetaHalf : eta ≤ (m / 2) * (1 - c⁻¹ ^ 2) := min_le_right _ _
  have hetaOld : eta ≤ m * (1 - c⁻¹ ^ 2) :=
    hetaHalf.trans (mul_le_mul_of_nonneg_right (by linarith) hfactor.le)
  have hscalar := scalar_uniform_near_time_on_compact hC F isCompact_univ t heta
  obtain ⟨K, _, hcompare⟩ := exists_compact_slab_metric_volume_comparison F
  have hE : Continuous (fun s : Icc a b => Real.exp (K * |s.val - t.val|)) :=
    Real.continuous_exp.comp
      (continuous_const.mul ((continuous_subtype_val.sub continuous_const).abs))
  have hmetric : ∀ᶠ s : Icc a b in 𝓝 t, Real.exp (K * |s.val - t.val|) < c :=
    hE.continuousAt.eventually (Iio_mem_nhds (by
      simpa only [sub_self, abs_zero, mul_zero, Real.exp_zero] using hc))
  filter_upwards [hscalar, hmetric] with s hs hEsmall
  intro y hy r hr hnorm
  have hycarrier : y ∈ N.carrier := by
    rw [N.core_eq_interior_closed_core] at hy
    have hclosed := interior_subset hy
    rw [N.closed_core_eq_complement_end] at hclosed
    exact hclosed.1
  have hnewfloor : m / 2 ≤ (F.connection s.val).scalarCurvature y := by
    have hdiff := (abs_lt.mp (hs y (mem_univ y))).1
    linarith [hlower y hycarrier]
  have hnormold : scalarCurvatureSupOn (F.metric t.val) (F.connection t.val)
      ((F.metric t.val).ball y (N.core_radius y)) = (N.core_radius y)⁻¹ ^ 2 := by
    simpa only [← hconnection] using N.core_radius_eq y hy
  have hdist (x z : M) :
      (F.metric s.val).edist x z ≤ ENNReal.ofReal c * (F.metric t.val).edist x z :=
    ((hcompare t.val t.property s.val s.property).2.1 x z).trans
      (mul_le_mul' (ENNReal.ofReal_le_ofReal hEsmall.le) le_rfl)
  have hdistBack (x z : M) :
      (F.metric t.val).edist x z ≤ ENNReal.ofReal c * (F.metric s.val).edist x z := by
    have h := (hcompare s.val s.property t.val t.property).2.1 x z
    rw [abs_sub_comm t.val s.val] at h
    exact h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hEsmall.le) le_rfl)
  constructor
  · have h := scalar_normalized_radius_le_of_close (F.metric t.val) (F.metric s.val)
      (F.connection t.val) (F.connection s.val) y (N.core_radius_pos y hy) hr
      hnormold hnorm hc.le hc hm (hlower y hycarrier) (hdist y)
      (fun z => by have h := (abs_lt.mp (hs z (mem_univ z))).1; linarith) hetaOld
    simpa only [hcc] using h
  · have h := scalar_normalized_radius_le_of_close (F.metric s.val) (F.metric t.val)
      (F.connection s.val) (F.connection t.val) y hr (N.core_radius_pos y hy)
      hnorm hnormold hc.le hc (half_pos hm) hnewfloor (hdistBack y)
      (fun z => by have h := (abs_lt.mp (hs z (mem_univ z))).2; linarith) hetaHalf
    simpa only [hcc] using h

end PoincareConjecture.Proofs.M47
