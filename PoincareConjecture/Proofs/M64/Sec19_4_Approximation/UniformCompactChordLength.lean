import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.RawLoopLength
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.SampledPolygonLength
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.HausdorffDensity.ChartComparison
import PoincareConjecture.Proofs.M09.TangentChartPhase
import PoincareConjecture.Proofs.M58.Cor18_28_PeriodicSpeed
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.CompactProductCover
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

noncomputable section

open Set Filter Metric Bundle MeasureTheory
open scoped Manifold ContDiff Topology BigOperators intervalIntegral NNReal ENNReal

universe u

namespace PoincareConjecture

open Proofs.M58

theorem m64_exists_uniform_sampled_chord_length
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M)
    (hcompact : IsCompact (univ : Set M))
    {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    (Gamma : Z → C1FreeLoopSpace (M := M))
    (hGamma : Continuous Gamma)
    {zeta : ℝ} (hzeta : 0 < zeta) :
    ∃ N0 : ℕ, 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ z : Z,
      let chord := ∑ j : Fin N,
        (g.edist
          (periodicFreeLoop (Gamma z) (m63CellLeft N j))
          (periodicFreeLoop (Gamma z) (m63CellLeft N (finRotate N j)))).toReal
      0 ≤ freeLoopLength g (Gamma z) - chord ∧
        freeLoopLength g (Gamma z) - chord < zeta := by
  classical
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  let : RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle LoopAmbient (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  let Y := Z × Icc (0 : ℝ) curvePeriod
  let gamma : Z → ℝ → M := fun z => periodicFreeLoop (Gamma z)
  let speed : Z → ℝ → ℝ := fun z t =>
    g.tangentNorm (gamma z t) (curveVelocity (gamma z) t)
  have hP : 0 < curvePeriod := Real.two_pi_pos
  have hgamma (z : Z) : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 (gamma z) :=
    contMDiff_periodicFreeLoop (Gamma z)
  have hperiod (z : Z) : Function.Periodic (gamma z) curvePeriod :=
    periodic_periodicFreeLoop (Gamma z)
  have hspeed (z : Z) : Continuous (speed z) :=
    continuous_freeLoopSpeed g (Gamma z)
  have hspeed0 (z : Z) (t : ℝ) : 0 ≤ speed z t := Real.sqrt_nonneg _
  have hjet : Continuous (fun w : Y => m63AngularFirstJet (gamma w.1) w.2) :=
    m63AngularFirstJet_continuous.comp
      ((hGamma.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
  have hvalue : Continuous (fun w : Y => gamma w.1 w.2) :=
    (FiberBundle.continuous_proj LoopAmbient (TangentSpace (𝓡 3))).comp hjet
  have hspeedJoint : Continuous (fun w : Y => speed w.1 w.2) :=
    (hjet.inner_bundle hjet).sqrt
  obtain ⟨S0, hS0⟩ := (isCompact_range hspeedJoint).bddAbove
  let S : ℝ := max S0 0
  let L : ℝ := S + 1
  have hS : 0 ≤ S := le_max_right _ _
  have hL : 0 < L := by dsimp only [L]; positivity
  have hSL : S ≤ L := le_add_of_nonneg_right zero_le_one
  have hspeedBound (w : Y) : speed w.1 w.2 ≤ S :=
    (hS0 (mem_range_self w)).trans (le_max_left _ _)
  let sigma : ℝ := min 1 (zeta / (16 * curvePeriod * L))
  have hsigma : 0 < sigma := lt_min zero_lt_one (div_pos hzeta (by positivity))
  have hsigma1 : sigma ≤ 1 := min_le_left _ _
  let K : ℝ≥0 := ⟨1 + sigma, by positivity⟩
  have hK : 1 < K := by change 1 < 1 + sigma; linarith only [hsigma]
  have hK0 : 0 ≤ (K : ℝ) := K.2
  have hK2 : (K : ℝ) ≤ 2 := by change 1 + sigma ≤ 2; linarith only [hsigma1]
  let d : ℝ := sigma * L
  have hd : 0 < d := mul_pos hsigma hL
  have htotal : 7 * sigma * L * curvePeriod < zeta := by
    have h := (le_div_iff₀ (show 0 < 16 * curvePeriod * L by positivity)).mp
      (min_le_right (1 : ℝ) (zeta / (16 * curvePeriod * L)))
    change sigma * (16 * curvePeriod * L) ≤ zeta at h
    nlinarith only [h, hzeta]
  let q : M → (LoopAmbient ≃L[ℝ] LoopAmbient) → Z → ℝ → LoopAmbient :=
    fun p A z t => A ((chartAt LoopAmbient p) (gamma z t))
  let bvec : M → (LoopAmbient ≃L[ℝ] LoopAmbient) → Z → ℝ → LoopAmbient :=
    fun p A z t => A (mfderiv (𝓡 3) (𝓡 3) (chartAt LoopAmbient p)
      (gamma z t) (curveVelocity (gamma z) t))
  have hder (p : M) (A : LoopAmbient ≃L[ℝ] LoopAmbient)
      (z : Z) (t : ℝ) (ht : gamma z t ∈ (chartAt LoopAmbient p).source) :
      HasDerivAt (q p A z) (bvec p A z t) t := by
    have hc := (mdifferentiable_chart (I := 𝓡 3) p).mdifferentiableAt ht
    have hg := (hgamma z t).mdifferentiableAt one_ne_zero
    have hdiff := mdifferentiableAt_iff_differentiableAt.mp (hc.comp t hg)
    have heq : deriv ((chartAt LoopAmbient p) ∘ gamma z) t =
        mfderiv (𝓡 3) (𝓡 3) (chartAt LoopAmbient p) (gamma z t)
          (curveVelocity (gamma z) t) := by
      simpa +instances only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv, curveVelocity]
        using! mfderiv_comp_apply t hc hg (1 : ℝ)
    have hh := hdiff.hasDerivAt
    rw [heq] at hh
    simpa +instances only [q, bvec, Function.comp_def] using!
      A.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hh

  have hlocal (w : Y) :
      ∃ p : M, ∃ A : LoopAmbient ≃L[ℝ] LoopAmbient, ∃ V : Set Y,
        IsOpen V ∧ w ∈ V ∧
        (∀ v ∈ V, gamma v.1 v.2 ∈ (chartAt LoopAmbient p).source ∧
          speed v.1 v.2 ≤ (K : ℝ) * ‖bvec p A v.1 v.2‖) ∧
        (∀ v ∈ V, ∀ v' ∈ V,
          ENNReal.ofReal ‖q p A v.1 v.2 - q p A v'.1 v'.2‖ ≤
            (K : ℝ≥0∞) * g.edist (gamma v.1 v.2) (gamma v'.1 v'.2)) ∧
        (∀ v ∈ V, ∀ v' ∈ V, ‖bvec p A v.1 v.2 - bvec p A v'.1 v'.2‖ ≤ d) := by
    let p : M := gamma w.1 w.2
    let c := chartAt LoopAmbient p
    let x0 := c p
    have hp : p ∈ c.source := mem_chart_source LoopAmbient p
    have hx0 : x0 ∈ c.target := c.map_source hp
    have hc : ContMDiffOn (𝓡 3) (𝓡 3) ∞ c c.source := contMDiffOn_chart
    have hci : ContMDiffOn (𝓡 3) (𝓡 3) ∞ c.symm c.target := contMDiffOn_chart_symm
    have hcinj : Function.Injective (mfderiv (𝓡 3) (𝓡 3) c.symm x0) :=
      ((mdifferentiable_chart (I := 𝓡 3) p).symm.mfderiv_bijective hx0).1
    obtain ⟨A, hA, _hdet⟩ := g.exists_frozenPullbackEquiv hcinj
    have hnear := g.eventually_pullbackNorm_comparison
      (hci.contMDiffAt (c.open_target.mem_nhds hx0)) A hA hK
    obtain ⟨U, hUopen, hxU, _hUsource, hdist⟩ :=
      g.exists_open_distortion_of_tangentNorm_comparison c.symm hci hc hx0 A hK hnear
    obtain ⟨U1, hU1sub, hU1open, hxU1⟩ := _root_.mem_nhds_iff.mp hnear
    let T : Set M := c.source ∩ c ⁻¹' (U ∩ U1)
    have hTopen : IsOpen T := c.isOpen_inter_preimage (hUopen.inter hU1open)
    have hpT : p ∈ T := ⟨hp, hxU, hxU1⟩
    have hsourceOpen : IsOpen {v : Y | gamma v.1 v.2 ∈ c.source} :=
      c.open_source.preimage hvalue
    have hphase := (Proofs.M09.tangentChartPhase_continuousOn p).comp
      hjet.continuousOn (show MapsTo (fun v : Y => m63AngularFirstJet (gamma v.1) v.2)
        {v : Y | gamma v.1 v.2 ∈ c.source}
        {v : TangentBundle (𝓡 3) M | v.proj ∈ c.source} from fun _ hv => hv)
    have hb : ContinuousOn (fun v : Y => bvec p A v.1 v.2)
        {v : Y | gamma v.1 v.2 ∈ c.source} :=
      A.continuous.comp_continuousOn hphase.snd
    have hbAt : ContinuousAt (fun v : Y => bvec p A v.1 v.2) w :=
      hb.continuousAt (hsourceOpen.mem_nhds hp)
    have hnb : ∀ᶠ v : Y in 𝓝 w,
        ‖bvec p A v.1 v.2 - bvec p A w.1 w.2‖ < d / 2 := by
      simpa only [dist_eq_norm] using Metric.tendsto_nhds.mp hbAt (d / 2) (half_pos hd)
    obtain ⟨V, hVsub, hVopen, hwV⟩ := _root_.mem_nhds_iff.mp
      (inter_mem (hvalue.continuousAt.preimage_mem_nhds (hTopen.mem_nhds hpT)) hnb)
    have hVT {v : Y} (hv : v ∈ V) : gamma v.1 v.2 ∈ T := (hVsub hv).1
    refine ⟨p, A, V, hVopen, hwV, ?_, ?_, ?_⟩
    · intro v hv
      have hvT := hVT hv
      refine ⟨hvT.1, ?_⟩
      have hback : mfderiv (𝓡 3) (𝓡 3) c.symm (c (gamma v.1 v.2))
          (mfderiv (𝓡 3) (𝓡 3) c (gamma v.1 v.2) (curveVelocity (gamma v.1) v.2)) =
            curveVelocity (gamma v.1) v.2 := by
        exact congrArg
          (fun L : TangentSpace (𝓡 3) (gamma v.1 v.2) →L[ℝ]
            TangentSpace (𝓡 3) (gamma v.1 v.2) => L (curveVelocity (gamma v.1) v.2))
          ((mdifferentiable_chart (I := 𝓡 3) p).symm_comp_deriv hvT.1)
      have htangent := (hU1sub hvT.2.2
        (mfderiv (𝓡 3) (𝓡 3) c (gamma v.1 v.2) (curveVelocity (gamma v.1) v.2))).2
      rw [hback, c.left_inv hvT.1] at htangent
      exact htangent
    · intro v hv v' hv'
      have h := (hdist _ (hVT hv).2.1 _ (hVT hv').2.1).2
      simpa only [c.left_inv (hVT hv).1, c.left_inv (hVT hv').1,
        edist_dist, dist_eq_norm] using h
    · intro v hv v' hv'
      have h1 : ‖bvec p A v.1 v.2 - bvec p A w.1 w.2‖ < d / 2 := (hVsub hv).2
      have h2 : ‖bvec p A v'.1 v'.2 - bvec p A w.1 w.2‖ < d / 2 := (hVsub hv').2
      have htri := norm_sub_le_norm_sub_add_norm_sub
        (bvec p A v.1 v.2) (bvec p A w.1 w.2) (bvec p A v'.1 v'.2)
      rw [norm_sub_rev (bvec p A w.1 w.2)] at htri
      linarith only [htri, h1, h2]
  choose p A V hVopen hVself hVspeed hVdist hVosc using hlocal
  obtain ⟨delta, hdelta, hcover⟩ := m64_compact_product_cover_vertical_radius
    (V := fun w : Y => V w) hVopen hVself
  have hshort (z : Z) {s t : ℝ}
      (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ curvePeriod) (hell : t - s < delta) :
      let I := ∫ u in s..t, speed z u
      let D := (g.edist (gamma z s) (gamma z t)).toReal
      0 ≤ I - D ∧ I - D ≤ 7 * sigma * L * (t - s) := by
    let ws : Y := (z, ⟨s, hs, hst.trans ht⟩)
    obtain ⟨w, hw⟩ := hcover ws
    have hcell (u : ℝ) (hu : u ∈ Icc s t) :
        (z, (⟨u, hs.trans hu.1, hu.2.trans ht⟩ : Icc (0 : ℝ) curvePeriod)) ∈ V w := by
      have hdiff : |u - s| < delta := by
        rw [abs_of_nonneg (sub_nonneg.mpr hu.1)]
        exact (sub_le_sub_right hu.2 s).trans_lt hell
      apply hw
      change |u - s| < delta
      exact hdiff
    let Q : ℝ → LoopAmbient := q (p w) (A w) z
    let B : ℝ → LoopAmbient := bvec (p w) (A w) z
    have hQ (u : ℝ) (hu : u ∈ Icc s t) : HasDerivAt Q (B u) u :=
      hder (p w) (A w) z u (hVspeed w _ (hcell u hu)).1
    have hB (u : ℝ) (hu : u ∈ Icc s t) : ‖B u - B s‖ ≤ d := by
      simpa +instances only [B] using!
        hVosc w _ (hcell u hu) _ (hcell s ⟨le_rfl, hst⟩)
    have hrem : ‖Q t - Q s - (t - s) • B s‖ ≤ d * (t - s) := by
      have hmean := norm_image_sub_le_of_norm_deriv_le_segment'
        (a := s) (b := t) (f := fun u => Q u - (u - s) • B s)
        (f' := fun u => B u - B s) (C := d)
        (fun u hu => by
          have hh := (hQ u hu).sub (((hasDerivAt_id u).sub_const s).smul_const (B s))
          simpa +instances only [one_smul, Pi.sub_apply, id_eq] using! hh.hasDerivWithinAt)
        (fun u hu => hB u (Ico_subset_Icc_self hu)) t ⟨hst, le_rfl⟩
      have heq : (Q t - (t - s) • B s) - (Q s - (s - s) • B s) =
          Q t - Q s - (t - s) • B s := by simp only [sub_self, zero_smul, sub_zero]; abel
      rwa [heq] at hmean
    let I : ℝ := ∫ u in s..t, speed z u
    let D : ℝ := (g.edist (gamma z s) (gamma z t)).toReal
    have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg hst (fun u _ => hspeed0 z u)
    have hD0 : 0 ≤ D := ENNReal.toReal_nonneg
    have hpath : g.edist (gamma z s) (gamma z t) ≤ ENNReal.ofReal I := by
      have h := g.edist_le_pathELength_of_mem_Icc (hgamma z).contMDiffOn
        (show t ∈ Icc s t from ⟨hst, le_rfl⟩)
      rw [M04.pathELength_eq_ofReal_integral_pathSpeed g (hgamma z) hst] at h
      exact h
    have hfinite : g.edist (gamma z s) (gamma z t) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hpath
    have hDI : D ≤ I := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hpath
      simpa only [ENNReal.toReal_ofReal hI0] using h
    have hIS : I ≤ S * (t - s) := by
      have h := intervalIntegral.integral_mono_on (μ := volume) hst
        ((hspeed z).intervalIntegrable s t) (continuous_const.intervalIntegrable s t)
        (fun u hu => hspeedBound (z, ⟨u, hs.trans hu.1, hu.2.trans ht⟩))
      simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h
    have hcoord : ‖Q t - Q s‖ ≤ (K : ℝ) * D := by
      have h := hVdist w _ (hcell t ⟨hst, le_rfl⟩) _ (hcell s ⟨le_rfl, hst⟩)
      have hedist : g.edist (gamma z t) (gamma z s) = g.edist (gamma z s) (gamma z t) :=
        Manifold.riemannianEDist_comm
      rw [hedist] at h
      have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hfinite) h
      simpa only [ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_mul,
        ENNReal.coe_toReal] using hr
    have hB0 : (t - s) * ‖B s‖ ≤ (K : ℝ) * D + d * (t - s) := by
      have htri := norm_add_le (Q t - Q s) ((t - s) • B s - (Q t - Q s))
      have heq : (Q t - Q s) + ((t - s) • B s - (Q t - Q s)) =
          (t - s) • B s := by abel
      rw [heq, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hst)] at htri
      have herr : ‖(t - s) • B s - (Q t - Q s)‖ ≤ d * (t - s) := by
        calc
          _ = ‖Q t - Q s - (t - s) • B s‖ := norm_sub_rev _ _
          _ ≤ _ := hrem
      exact htri.trans (add_le_add hcoord herr)
    have hvK (u : ℝ) (hu : u ∈ Icc s t) : speed z u ≤ (K : ℝ) * (‖B s‖ + d) := by
      have hn := norm_add_le (B u - B s) (B s)
      rw [sub_add_cancel] at hn
      have hb : ‖B u‖ ≤ ‖B s‖ + d := by linarith only [hn, hB u hu]
      exact (hVspeed w _ (hcell u hu)).2.trans (mul_le_mul_of_nonneg_left hb hK0)
    have hIK : I ≤ (K : ℝ) * (‖B s‖ + d) * (t - s) := by
      have h := intervalIntegral.integral_mono_on (μ := volume) hst
        ((hspeed z).intervalIntegrable s t) (continuous_const.intervalIntegrable s t) hvK
      simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h
    have hdeficit : I - D ≤ ((K : ℝ) ^ 2 - 1) * D + 2 * (K : ℝ) * d * (t - s) := by
      have h := mul_le_mul_of_nonneg_left hB0 hK0
      nlinarith only [hIK, h]
    have hKsq : (K : ℝ) ^ 2 - 1 ≤ 3 * sigma := by
      have hsq := mul_le_mul_of_nonneg_left hsigma1 hsigma.le
      change (1 + sigma) ^ 2 - 1 ≤ 3 * sigma
      nlinarith only [hsq]
    have hfirst : ((K : ℝ) ^ 2 - 1) * D ≤ 3 * sigma * S * (t - s) := by
      calc
        _ ≤ (3 * sigma) * D := mul_le_mul_of_nonneg_right hKsq hD0
        _ ≤ (3 * sigma) * (S * (t - s)) :=
          mul_le_mul_of_nonneg_left (hDI.trans hIS) (by positivity)
        _ = _ := by ring
    have hsecond : 2 * (K : ℝ) * d * (t - s) ≤ 4 * sigma * L * (t - s) := by
      have h := mul_le_mul_of_nonneg_right hK2 (mul_nonneg hd.le (sub_nonneg.mpr hst))
      dsimp only [d] at h ⊢
      nlinarith only [h]
    refine ⟨sub_nonneg.mpr hDI, hdeficit.trans ?_⟩
    have hSL' := mul_le_mul_of_nonneg_left hSL
      (show 0 ≤ 3 * sigma * (t - s) by positivity)
    nlinarith only [hfirst, hsecond, hSL']
  obtain ⟨N0, hN0⟩ := exists_nat_gt (max 1 (curvePeriod / delta))
  have hN0pos : 0 < N0 := by
    have h : (0 : ℝ) < N0 := zero_lt_one.trans ((le_max_left _ _).trans_lt hN0)
    exact_mod_cast h
  refine ⟨N0, hN0pos, ?_⟩
  intro N hN z
  have hNpos : 0 < N := hN0pos.trans_le hN
  have hell : 0 < m63CellLength N := m63CellLength_pos hNpos
  have hmesh : m63CellLength N < delta := by
    change curvePeriod / (N : ℝ) < delta
    have h0 := (div_lt_iff₀ hdelta).mp ((le_max_right _ _).trans_lt hN0)
    have hcast : (N0 : ℝ) ≤ N := by exact_mod_cast hN
    apply (div_lt_iff₀ (show (0 : ℝ) < N by exact_mod_cast hNpos)).mpr
    exact h0.trans_le (by nlinarith only [mul_le_mul_of_nonneg_right hcast hdelta.le])
  have hcell (j : Fin N) :
      0 ≤ (∫ u in m63CellLeft N j..m63CellLeft N j + m63CellLength N, speed z u) -
        (g.edist (gamma z (m63CellLeft N j))
          (gamma z (m63CellLeft N (finRotate N j)))).toReal ∧
      (∫ u in m63CellLeft N j..m63CellLeft N j + m63CellLength N, speed z u) -
        (g.edist (gamma z (m63CellLeft N j))
          (gamma z (m63CellLeft N (finRotate N j)))).toReal ≤
        7 * sigma * L * m63CellLength N := by
    have hs : 0 ≤ m63CellLeft N j := mul_nonneg (Nat.cast_nonneg _) hell.le
    have horder : m63CellLeft N j ≤ m63CellLeft N j + m63CellLength N :=
      le_add_of_nonneg_right hell.le
    have hright : m63CellLeft N j + m63CellLength N ≤ curvePeriod := by
      have hcast : (j.val : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt j.isLt
      calc
        _ = ((j.val : ℝ) + 1) * m63CellLength N := by dsimp only [m63CellLeft]; ring
        _ ≤ (N : ℝ) * m63CellLength N := mul_le_mul_of_nonneg_right hcast hell.le
        _ = curvePeriod := m63_count_mul_cellLength hNpos
    have hh := hshort z hs horder hright (by simpa only [add_sub_cancel_left] using hmesh)
    rw [m63PeriodicLoop_cell_finish (hperiod z) hNpos j]
    simpa only [add_sub_cancel_left] using hh
  have hsum : (∑ j : Fin N,
      ∫ u in m63CellLeft N j..m63CellLeft N j + m63CellLength N, speed z u) =
        freeLoopLength g (Gamma z) := by
    have htel := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ => (k : ℝ) * m63CellLength N) (n := N) (μ := volume)
      (fun _ _ => (hspeed z).intervalIntegrable _ _)
    rw [← Fin.sum_univ_eq_sum_range] at htel
    simpa only [m63CellLeft, Nat.cast_add, Nat.cast_one, add_mul, one_mul,
      Nat.cast_zero, zero_mul, m63_count_mul_cellLength hNpos, curvePeriod,
      freeLoopLength, rampPeriod, speed, gamma] using htel
  have hsumLength : (∑ _j : Fin N, m63CellLength N) = curvePeriod := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      curvePeriod]
      using m63_count_mul_cellLength hNpos
  have hnon := Finset.sum_nonneg (fun j (_hj : j ∈ (Finset.univ : Finset (Fin N))) =>
    (hcell j).1)
  have hle := Finset.sum_le_sum (fun j (_hj : j ∈ (Finset.univ : Finset (Fin N))) =>
    (hcell j).2)
  rw [Finset.sum_sub_distrib, hsum] at hnon hle
  rw [← Finset.mul_sum, hsumLength] at hle
  exact ⟨hnon, hle.trans_lt htotal⟩

end PoincareConjecture
