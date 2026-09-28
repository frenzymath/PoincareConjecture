import PoincareConjecture.Proofs.M35.RadialGauge.MovingPullbackDerivative
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawJointRegularity
import PoincareConjecture.Proofs.M03.Existence.PullbackRicciNative










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.RadialGauge

open Uniqueness Uniqueness.Heat DeTurckNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)



theorem nativeDeTurckField_contDiff {g b : RiemannianMetric n V}
    (K : LeviCivitaData g) (B : LeviCivitaData b) :
    ContDiff ℝ ∞ (intrinsicDeTurckField K B) := by
  have h : ContMDiff (𝓡 n) (𝓡 n) ∞ (intrinsicDeTurckField K B) := by
    intro x
    simpa only [trivializationAt_model_space_apply] using!
      (Bundle.contMDiffAt_totalSpace.mp ((intrinsicDeTurckField_contMDiff K B) x)).2
  exact contMDiff_iff_contDiff.mp h



theorem inverse_pullback_solves_native_deturck
    {J : Set ℝ} (F : RicciFlow n V J)
    {Φ : ℝ → Diffeomorph (𝓡 n) (𝓡 n) V V ∞} {I : Set ℝ} (hI : IsOpen I)
    (hΦ : ContDiffOn ℝ 2 (fun p : ℝ × V => Φ p.1 p.2) (I ×ˢ univ))
    {t₀ t : ℝ} (ht : t ∈ I) (hJ : J ∈ 𝓝 (t₀ + t))
    {b : RiemannianMetric n V} (B : LeviCivitaData b)
    (K : LeviCivitaData (gaugePullbackMetric (F.metric (t₀ + t)) (Φ t).symm))
    (hvelocity : ∀ z : V, HasDerivAt (fun s => Φ s z)
      (-intrinsicDeTurckField K B (Φ t z)) t) (x u v : V) :
    HasDerivAt
      (fun s => (gaugePullbackMetric (F.metric (t₀ + s)) (Φ s).symm).inner x u v)
      (-2 * K.ricci x u v + metricLieDerivative K (intrinsicDeTurckField K B) x u v) t := by
  have hcoeff : ContDiffOn ℝ ∞
      (fun p : ℝ × V => (F.metric p.1).euclideanCoefficients p.2) (J ×ˢ univ) := by
    apply contDiffOn_clm_apply.mpr
    intro a
    apply contDiffOn_clm_apply.mpr
    intro c
    exact raw_metric_pair_family_contDiffOn F a c
  have hcoeffAt : ContDiffAt ℝ 1
      (fun p : ℝ × V => (F.metric (t₀ + p.1)).euclideanCoefficients p.2)
      (t, (Φ t).symm x) := by
    have hbase : ContDiffAt ℝ ∞
        (fun p : ℝ × V => (F.metric p.1).euclideanCoefficients p.2)
        (t₀ + t, (Φ t).symm x) :=
      hcoeff.contDiffAt (prod_mem_nhds hJ (univ_mem))
    exact ((hbase.comp (t, (Φ t).symm x)
      ((contDiffAt_const.add contDiffAt_fst).prodMk contDiffAt_snd))).of_le
        (WithTop.coe_le_coe.mpr le_top)
  have hsource (a c : V) : HasDerivAt
      (fun s => (F.metric (t₀ + s)).inner ((Φ t).symm x) a c)
      (-2 * (F.connection (t₀ + t)).ricci ((Φ t).symm x) a c) t := by
    have hd := (F.equation (t₀ + t) (mem_of_mem_nhds hJ)
      ((Φ t).symm x) a c).hasDerivAt hJ
    simpa only [Function.comp_def, one_mul, mul_one] using
      hd.comp t ((hasDerivAt_id t).const_add t₀)
  have h := inverse_pullback_metric_pair_hasDerivAt hI hΦ ht
    (nativeDeTurckField_contDiff K B) hvelocity x u v hcoeffAt hsource K
  have hricci : K.ricci x u v = (F.connection (t₀ + t)).ricci ((Φ t).symm x)
      (fderiv ℝ ((Φ t).symm : V → V) x u)
      (fderiv ℝ ((Φ t).symm : V → V) x v) := by
    simpa only [mfderiv_eq_fderiv] using!
      ricci_pullback (F.metric (t₀ + t)) (Φ t).symm
        (contMDiff_gaugePullback_section (F.metric (t₀ + t)) (Φ t).symm)
        (F.connection (t₀ + t)) K x u v
  rwa [← hricci] at h

end PoincareConjecture.M35.RadialGauge
