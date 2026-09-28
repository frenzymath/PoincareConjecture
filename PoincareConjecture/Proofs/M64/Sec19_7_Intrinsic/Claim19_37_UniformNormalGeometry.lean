import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_EndpointPeriodicity
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_NormalDensity
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_EndpointLift

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle Matrix

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_exists_uniform_normal_geometry
    (K : ℝ) {delta alpha : ℝ} (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (halpha : 0 ≤ alpha) :
    ∃ R0 : ℝ, 0 < R0 ∧ R0 < 1 / 10 ∧
      ∀ R : ℝ, 0 < R → R ≤ R0 →
        ∀ N : IntrinsicAnnulus, N.GaussianCurvatureBound K →
          ∃ (normal : ℝ → AnnulusCoordinates)
            (e : AnnulusCoordinates → AnnulusCoordinates) (height : ℝ → ℝ),
            ContDiff ℝ ∞ normal ∧ ContDiff ℝ ∞ e ∧ Measurable height ∧
            Function.Periodic normal rampPeriod ∧
            (∀ t : ℝ, Function.Periodic (fun a => e !₂[a, t]) rampPeriod) ∧
            Function.Periodic height rampPeriod ∧
            (∀ a, N.metric.inner (intrinsicAnnulusBoundary 1 a) (normal a) (normal a) = 1 ∧
              N.metric.inner (intrinsicAnnulusBoundary 1 a) (normal a)
                (curveVelocity (n := 2) (intrinsicAnnulusBoundary 1) a) = 0 ∧
              0 < inner ℝ (intrinsicAnnulusBoundary 1 a) (normal a)) ∧
            (∀ a, e !₂[a, 0] = intrinsicAnnulusBoundary 1 a) ∧
            (∀ a, HasDerivAt (fun t => e !₂[a, t]) (normal a) 0) ∧
            (∀ a, 0 < height a ∧ height a ≤ R ∧
              (∀ t ∈ Ioo (0 : ℝ) (height a), 1 < ‖e !₂[a, t]‖ ∧ ‖e !₂[a, t]‖ < 2) ∧
              e !₂[a, height a] ∈ standardAnnulusDomain ∧
              (height a = R ∨ ‖e !₂[a, height a]‖ = 1 ∨ ‖e !₂[a, height a]‖ = 2)) ∧
            (∀ a, ∃ S I : Set ℝ, IsOpen S ∧ IsOpen I ∧ a ∈ S ∧
              Icc (0 : ℝ) (height a) ⊆ I ∧
              ∀ s ∈ S, N.metric.IsGeodesicOn (fun t => e !₂[s, t]) I) ∧
            ∀ a, intrinsicGeodesicCurvature N.metric N.connection 1 a ≤ alpha →
              ∀ t ∈ Icc (0 : ℝ) (height a),
                (∀ v : AnnulusCoordinates,
                  (1 - delta) ^ 2 *
                    (intrinsicBoundarySpeed N.metric 1 a ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
                    N.metric.inner (e !₂[a, t])
                      (fderiv ℝ e !₂[a, t] v) (fderiv ℝ e !₂[a, t] v)) ∧
                Function.Injective (fderiv ℝ e !₂[a, t]) ∧
                (1 - delta) ^ 2 * intrinsicBoundarySpeed N.metric 1 a ≤
                  N.metric.pullbackVolumeDensity e !₂[a, t] := by
  obtain ⟨R0, hR0, hR0small, hmetric⟩ :=
    m64Intrinsic_exists_uniform_normal_metric_radius K hdelta hdelta1 halpha
  refine ⟨R0, hR0, hR0small, ?_⟩
  intro R hR hRR0 N hK
  obtain ⟨G, normal, u, hG, hnormal, hu, hn, hend⟩ :=
    m64Intrinsic_exists_smooth_extended_normal_endpoint N
  have hdata := m64Intrinsic_normal_endpoint_initial_data G hend
  have hnperiod := m64Intrinsic_inward_normal_periodic N hn
  have huperiod := m64Intrinsic_normal_endpoint_periodic G hnperiod hend
  obtain ⟨height, hheight, hcontact⟩ := m64Intrinsic_exists_measurable_contact_times
    hu.continuous hR (fun a => m64Intrinsic_inward_curve_enters_annulus
      (hdata a).1 (hdata a).2 (hn a).2.2)
  have hheightPeriod : Function.Periodic height rampPeriod :=
    m64Intrinsic_first_contact_height_periodic huperiod (fun a =>
      ⟨(hcontact a).1, (hcontact a).2.1, (hcontact a).2.2.1, (hcontact a).2.2.2.2⟩)
  let e : AnnulusCoordinates → AnnulusCoordinates := fun z => u (z 0, z 1)
  have he : ContDiff ℝ ∞ e := hu.comp (by fun_prop)
  have himage (a : ℝ) :
      ∀ t ∈ Icc (0 : ℝ) (height a), u (a, t) ∈ standardAnnulusDomain := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with hzero | hpos
    · rw [← hzero, (hdata a).1]
      have hnorm : ‖intrinsicAnnulusBoundary 1 a‖ = 1 := by
        have hsq := m64Intrinsic_boundary_self_inner 1 a
        rw [real_inner_self_eq_norm_sq] at hsq
        nlinarith [norm_nonneg (intrinsicAnnulusBoundary 1 a)]
      exact ⟨by rw [hnorm], by simpa only [hnorm] using (by norm_num : (1 : ℝ) ≤ 2)⟩
    · rcases eq_or_lt_of_le ht.2 with hlast | hlt
      · simpa only [hlast] using (hcontact a).2.2.2.1
      · exact ⟨((hcontact a).2.2.1 t ⟨hpos, hlt⟩).1.le,
          ((hcontact a).2.2.1 t ⟨hpos, hlt⟩).2.le⟩
  have htube (a : ℝ) : ∃ S I : Set ℝ, IsOpen S ∧ IsOpen I ∧ a ∈ S ∧
      Icc (0 : ℝ) (height a) ⊆ I ∧
      ∀ s ∈ S, N.metric.IsGeodesicOn (fun t => u (s, t)) I := by
    have hsmall : height a < 1 := ((hcontact a).2.1.trans hRR0).trans_lt
      (hR0small.trans (by norm_num))
    obtain ⟨S, I, hS, hI, ha, hsub, _, hgeo⟩ :=
      m64Intrinsic_exists_actual_normal_geodesic_neighborhood N G hG hnormal hu hend
        hsmall (himage a)
    exact ⟨S, I, hS, hI, ha, hsub, hgeo⟩
  refine ⟨normal, e, height, hnormal, he, hheight, hnperiod, huperiod, hheightPeriod,
    hn, fun a => (hdata a).1, fun a => (hdata a).2, hcontact, htube, ?_⟩
  intro a ha
  obtain ⟨S, I, hS, hI, haS, hsub, hgeo⟩ := htube a
  have hbound := hmetric (height a) (hcontact a).1 ((hcontact a).2.1.trans hRR0)
    N 1 (by norm_num) hK u S I hS hI hsub
    (contMDiff_iff_contDiff.mpr hu).contMDiffOn hgeo (fun s _ => (hdata s).1)
    normal hnormal (fun s => (hn s).1) (fun s => (hn s).2.1)
    (fun s _ => (m64Intrinsic_curveVelocity_eq_deriv _ _).trans (hdata s).2.deriv)
    a haS ha (fun t ht =>
      ⟨((hcontact a).2.2.1 t ht).1.le, ((hcontact a).2.2.1 t ht).2.le⟩)
  intro t ht
  have hd (v : AnnulusCoordinates) :
      fderiv ℝ e !₂[a, t] v = fderiv ℝ u (a, t) (v 0, v 1) :=
    m64Intrinsic_normal_coordinate_differential (hu.differentiable (by simp) (a, t)) v
  refine ⟨?_, ?_, ?_⟩
  · intro v
    rw [hd]
    exact (hbound t ht).1 (v 0, v 1)
  · intro v w hvw
    rw [hd, hd] at hvw
    have heq := (hbound t ht).2 hvw
    ext i
    fin_cases i
    · exact congrArg Prod.fst heq
    · exact congrArg Prod.snd heq
  · exact m64Intrinsic_normal_map_density_lower N.metric
      (hu.differentiable (by simp) (a, t)) (hbound t ht).1

end PoincareConjecture
