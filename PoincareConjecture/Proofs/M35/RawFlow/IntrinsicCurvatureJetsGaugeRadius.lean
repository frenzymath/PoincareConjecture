import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsGaugeExistence
import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsGaugeEquation
import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsGaugeTimeJets
import PoincareConjecture.Proofs.M35.RadialGauge.RadialTraceJets
import PoincareConjecture.Proofs.M35.RadialGauge.UniformRadiusEnd
import PoincareConjecture.Proofs.M35.RadialGauge.GaugeRestriction
import PoincareConjecture.Proofs.M35.RadialGauge.RadiusInverseTime
import PoincareConjecture.Proofs.M35.RadialGauge.RestrictedMapJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

open RadialGauge

theorem exists_raw_intrinsic_corrected_radial_gauge
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (H : StandardCapEstimate g₀) (G : PartialStandardCapFlow g₀)
    (hrotation : ∀ t ∈ Ico 0 G.lifetime,
      ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ x u v : StandardCapSpace,
        (G.flow.metric t).inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G.flow.metric t).inner x u v)
    {T t₀ : ℝ} (hT : 0 < T) (hTlt : T < G.lifetime) (ht₀ : t₀ ∈ Ico 0 T) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ T - t₀ ∧ ∃ w : ℝ → ℝ → ℝ,
      w 0 = 0 ∧ Continuous (fun p : Icc 0 delta × ℝ => w p.1.1 p.2) ∧
      (∀ t ∈ Icc 0 delta, ContDiff ℝ ∞ (w t) ∧ Function.Even (w t) ∧
        (∀ r, (1 + |r|) * |w t r| ≤ 1 / 8 ∧
          (1 + |r|) * |deriv (w t) r| ≤ 1 / 8) ∧
        (∀ r, 1 / 2 ≤ deriv (mapRadius (w t)) r ∧ |mapRadius (w t) r - r| ≤ 1 / 4) ∧
        (∃ q : ℝ → ℝ, ContDiff ℝ ∞ q ∧
          (∀ r, q (mapRadius (w t) r) = r) ∧ (∀ r, mapRadius (w t) (q r) = r)) ∧
        ∃ Φ : Diffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞,
          ∀ x, Φ x = Real.exp (w t ‖x‖) • x) ∧
      (∃ H J : ℝ, 0 ≤ H ∧ 0 ≤ J ∧ ∀ t ∈ Icc 0 delta, ∀ r,
        (1 + |r|) * |deriv (deriv (w t)) r| ≤ H ∧
        (1 + |r|) * |deriv (deriv (deriv (w t))) r| ≤ J) ∧
      (∀ epsilon > 0, ∃ R : ℝ, ∀ t ∈ Icc 0 delta, ∀ r, R ≤ |r| →
        (1 + |r|) * |deriv (w t) r| < epsilon ∧
        (1 + |r|) * |deriv (deriv (w t)) r| < epsilon) ∧
      ContDiffOn ℝ 1 (Function.uncurry w) (Ioo 0 delta ×ˢ univ) ∧
      (ContDiffOn ℝ 1
        (fun p : ℝ × StandardCapSpace => euclideanGauge (fun x => w p.1 ‖x‖) p.2)
        (Ioo 0 delta ×ˢ univ) ∧
      ContDiffOn ℝ 1
        (fun p : ℝ × StandardCapSpace => fderiv ℝ (euclideanGauge (fun x => w p.1 ‖x‖)) p.2)
        (Ioo 0 delta ×ˢ univ) ∧
      ContDiffOn ℝ 1
        (fun p : ℝ × StandardCapSpace =>
          fderiv ℝ (fderiv ℝ (euclideanGauge (fun x => w p.1 ‖x‖))) p.2)
        (Ioo 0 delta ×ˢ univ)) ∧
      (∀ t ∈ Ioo 0 delta, ∀ s > 0,
        HasDerivAt (fun a => mapRadiusInverse w a s)
          (-harmonicRadialOperator 3 (rawWarpingRadius P G hrotation (t₀ + t))
            (rawWarpingRadius P G hrotation t₀) (rawRadialVelocity P G hrotation (t₀ + t))
            (mapRadius (w t)) (mapRadiusInverse w t s) /
              deriv (mapRadius (w t)) (mapRadiusInverse w t s)) t) ∧
      ∀ t ∈ Ioo 0 delta, ∀ r > 0, HasDerivAt (fun s => mapRadius (w s) r)
        (harmonicRadialOperator 3 (rawWarpingRadius P G hrotation (t₀ + t))
          (rawWarpingRadius P G hrotation t₀) (rawRadialVelocity P G hrotation (t₀ + t))
          (mapRadius (w t)) r) t := by
  obtain ⟨delta, hd, hdT, u, hu0, hcu, hcdu, hub, hu, hbound, hend, hPDE⟩ :=
    exists_raw_intrinsic_smooth_gauge P H G hrotation hT hTlt ht₀
  let e := EuclideanSpace.basisFun (Fin 5) ℝ 0
  have he : ‖e‖ = 1 := (EuclideanSpace.basisFun (Fin 5) ℝ).norm_eq_one 0
  let w (t r : ℝ) := u t (r • e)
  have hnorm (r : ℝ) : ‖r • e‖ = |r| := by
    rw [norm_smul, he, mul_one, Real.norm_eq_abs]
  have hs (t : ℝ) (ht : t ∈ Icc 0 delta) :
      ContDiff ℝ ∞ (w t) ∧ Function.Even (w t) :=
    smooth_even_radial_trace (hu t ht).1 (hu t ht).2.1 e
  have hw (t : ℝ) (ht : t ∈ Icc 0 delta) (r : ℝ) :
      (1 + |r|) * |w t r| ≤ 1 / 8 ∧
      (1 + |r|) * |deriv (w t) r| ≤ 1 / 8 := by
    constructor
    · simpa only [w, hnorm, Real.norm_eq_abs] using ((hu t ht).2.2.1 (r • e)).1
    · have h := radialTrace_weighted_jet_le (hu t ht).1 he 1 r
      simp only [iteratedDeriv_one, norm_iteratedFDeriv_one] at h
      exact h.trans ((hu t ht).2.2.1 (r • e)).2
  have hjet (t : ℝ) (ht : t ∈ Icc 0 delta) (j : ℕ) (r : ℝ) :=
    radialTrace_weighted_jet_le (hu t ht).1 he j r
  have hreg := raw_intrinsic_gauge_spatial_time_jets P H G hrotation hT hTlt ht₀
    hd.le hdT hcu hcdu (fun t ht => (hu t ht).1) hub
    (fun t ht x => ((hu t ht).2.2.1 x).1) (fun t ht => (hu t ht).2.2.2.1)
  have hwjoint : ContDiffOn ℝ 1 (Function.uncurry w) (Ioo 0 delta ×ˢ univ) := by
    exact hreg.2.2.1.comp
      (contDiffOn_fst.prodMk (contDiffOn_snd.smul contDiffOn_const))
      (fun p hp => ⟨hp.1, mem_univ _⟩)
  have hmapjets := restricted_euclideanGauge_jets_joint_c1 (n := 2)
    threeIntoFive.toContinuousLinearMap
    (fun t ht => (hu t ⟨ht.1.le, ht.2.le⟩).1) hreg.2.2.1 hreg.2.2.2
  have hmapeq (t : ℝ) (ht : t ∈ Ioo 0 delta) :
      euclideanGauge (fun x : StandardCapSpace => u t (threeIntoFive.toContinuousLinearMap x)) =
        euclideanGauge (fun x : StandardCapSpace => w t ‖x‖) := by
    funext x
    have hscalar : u t (threeIntoFive x) = w t ‖x‖ :=
      orthogonal_invariant_eq_of_norm_eq (hu t ⟨ht.1.le, ht.2.le⟩).2.1
        (by rw [threeIntoFive.norm_map, hnorm, abs_norm])
    change Real.exp (u t (threeIntoFive x)) • x = Real.exp (w t ‖x‖) • x
    rw [hscalar]
  have hradius (t : ℝ) (ht : t ∈ Ioo 0 delta) (r : ℝ) (hr : 0 < r) :
      HasDerivAt (fun s => mapRadius (w s) r)
        (harmonicRadialOperator 3 (rawWarpingRadius P G hrotation (t₀ + t))
          (rawWarpingRadius P G hrotation t₀) (rawRadialVelocity P G hrotation (t₀ + t))
          (mapRadius (w t)) r) t := by
    have htcc : t ∈ Icc 0 delta := ⟨ht.1.le, ht.2.le⟩
    have htime : t₀ + t ∈ Icc 0 T := by
      constructor
      · exact add_nonneg ht₀.1 ht.1.le
      · linarith only [ht.2.le, hdT]
    exact raw_intrinsic_radius_time_equation P G hrotation hTlt
      ⟨ht₀.1, ht₀.2.le⟩ htime (hu t htcc).1 (hu t htcc).2.1 he hr (hPDE t ht (r • e))
  refine ⟨delta, hd, hdT, w, ?_, ?_, ?_, ?_, ?_, hwjoint, ?_, ?_, hradius⟩
  · funext r
    exact congrFun hu0 (r • e)
  · exact hcu.comp (continuous_fst.prodMk (continuous_snd.smul continuous_const))
  · intro t ht
    refine ⟨(hs t ht).1, (hs t ht).2, hw t ht, ?_, ?_, ?_⟩
    · intro r
      have hderiv := mapRadius_deriv_sub_one_bound (hs t ht).1 r
        (hw t ht r).1 (hw t ht r).2
      have hvalue := mapRadius_sub_self_bound (by norm_num : (1 / 8 : ℝ) ≤ 1)
        (hw t ht r).1
      exact ⟨by linarith only [(abs_le.mp hderiv).1], by norm_num at hvalue ⊢; exact hvalue⟩
    · exact exists_mapRadius_smooth_inverse (hs t ht).1
        (fun r => (hw t ht r).1) (fun r => (hw t ht r).2)
    · obtain ⟨Φ, hΦ⟩ := exists_three_dimensional_gauge (hu t ht).1
        (fun x => by simpa only [Real.norm_eq_abs] using ((hu t ht).2.2.1 x).1)
        (fun x => ((hu t ht).2.2.1 x).2)
      refine ⟨Φ, fun x => ?_⟩
      have hscalar : u t (threeIntoFive x) = w t ‖x‖ :=
        orthogonal_invariant_eq_of_norm_eq (hu t ht).2.1
          (by rw [threeIntoFive.norm_map, hnorm, abs_norm])
      rw [hΦ x, hscalar]
  · obtain ⟨H, J, hH, hJ, hHJ⟩ := hbound
    refine ⟨H, J, hH, hJ, ?_⟩
    intro t ht r
    have h2 := hjet t ht 2 r
    have h3 := hjet t ht 3 r
    simp only [iteratedDeriv_succ', iteratedDeriv_zero,
      ← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero] at h2 h3
    exact ⟨h2.trans (hHJ t ht (r • e)).1, h3.trans (hHJ t ht (r • e)).2⟩
  · intro epsilon hepsilon
    obtain ⟨R, hR⟩ := hend epsilon hepsilon
    refine ⟨R, fun t ht r hr => ?_⟩
    have h1 := hjet t ht 1 r
    have h2 := hjet t ht 2 r
    simp only [iteratedDeriv_succ', iteratedDeriv_zero,
      ← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero] at h1 h2
    have hr' : R ≤ ‖r • e‖ := by simpa only [hnorm] using hr
    exact ⟨h1.trans_lt (hR t ht (r • e) hr').1, h2.trans_lt (hR t ht (r • e) hr').2⟩
  · exact ⟨hmapjets.1.congr (fun p hp => by rw [hmapeq p.1 hp.1]),
      hmapjets.2.1.congr (fun p hp => by rw [hmapeq p.1 hp.1]),
      hmapjets.2.2.congr (fun p hp => by rw [hmapeq p.1 hp.1])⟩
  · intro t ht s hsz
    have htcc : t ∈ Icc 0 delta := ⟨ht.1.le, ht.2.le⟩
    have hinv := mapRadius_inverse_properties (hs t htcc).1
      (fun r => (hw t htcc r).1) (fun r => (hw t htcc r).2)
    have hpos : 0 < mapRadiusInverse w t s := inverse_mapRadius_pos hinv.2.2.1 hsz
    exact mapRadiusInverse_hasDerivAt_time isOpen_Ioo hwjoint
      (fun a ha => (hs a ⟨ha.1.le, ha.2.le⟩).1)
      (fun a ha r => (hw a ⟨ha.1.le, ha.2.le⟩ r).1)
      (fun a ha r => (hw a ⟨ha.1.le, ha.2.le⟩ r).2) ht
      (hradius t ht (mapRadiusInverse w t s) hpos)

end PoincareConjecture.M35.Uniqueness
