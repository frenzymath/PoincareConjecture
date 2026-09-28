import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUAlphaLocalComparison
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUAlphaWeakCompactness
import Mathlib.MeasureTheory.Function.UniformIntegrable



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

noncomputable section

universe u

namespace PoincareConjecture.M60

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem suAlpha_minimizing_weighted_cauchy
    (g : RiemannianMetric n M) {alpha R a C : ℝ} (ha : 1 ≤ alpha) (ha0 : 0 < a)
    (hC : 0 ≤ C) (p : UnitTwoSphere) (b : M)
    (e : M → EuclideanSpace ℝ (Fin n)) (he : ContMDiff (𝓡 n) (𝓡 n) ∞ e)
    (f : ℕ → UnitTwoSphere → M) (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) ∞ (f j))
    (hn : ∀ j, ¬ IsNullHomotopicSphere (f j))
    (henergy : Tendsto (fun j => m60SphereAlphaEnergy g alpha (f j)) atTop
      (𝓝 (sInf (m60NonNullAlphaEnergyValues g alpha))))
    (u0 : LoopPlane → EuclideanSpace ℝ (Fin n))
    (hlim : TendstoUniformly (fun j => e ∘ f j ∘ (chartAt LoopPlane p).symm) u0 atTop)
    (rho : UnitTwoSphere → ℝ) (hrho : ContMDiff (𝓡 2) 𝓘(ℝ) ∞ rho)
    (hrange : ∀ x, rho x ∈ Icc 0 (1 / 2))
    (hsupp : tsupport rho ⊆ (chartAt LoopPlane p).source ∩
      (chartAt LoopPlane p) ⁻¹' Metric.ball ((chartAt LoopPlane p) p) R)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : Convex ℝ K)
    (hKt : K ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) b).target)
    (hcoord : ∀ᶠ j in atTop, ∀ x ∈ (chartAt LoopPlane p).source ∩
      (chartAt LoopPlane p) ⁻¹' Metric.ball ((chartAt LoopPlane p) p) R,
      f j x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) b).source ∧
        e (f j x) = (chartAt (EuclideanSpace ℝ (Fin n)) b) (f j x) ∧ e (f j x) ∈ K)
    (hmetric : ∀ y ∈ K, ∀ v, a * ‖v‖ ^ 2 ≤
      g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm y v v)
    (hnorm : ∀ y ∈ K,
      ‖g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm y‖ ≤ C)
    (hmetriccont : UniformContinuousOn
      (g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm) K) :
    ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N,
      (∫ z in Metric.ball ((chartAt LoopPlane p) p) R,
        rho ((chartAt LoopPlane p).symm z) *
          ‖suAlphaDerivativePair (e ∘ f j ∘ (chartAt LoopPlane p).symm) z -
            suAlphaDerivativePair (e ∘ f k ∘ (chartAt LoopPlane p).symm) z‖ ^
              (2 * alpha)) ≤ eps := by
  let cs := chartAt LoopPlane p
  let O := Metric.ball (cs p) R
  let eta := rho ∘ cs.symm
  let m := sInf (m60NonNullAlphaEnergyValues g alpha)
  let c0 := (a / 4) ^ alpha
  have hc0 : 0 < c0 := Real.rpow_pos_of_pos (by positivity) _
  have heta : ContDiff ℝ ∞ eta := contMDiff_iff_contDiff.mp (hrho.comp (suSphereChart_smooth p))
  have hder : Continuous (fun z => ‖fderiv ℝ eta z‖) :=
    (heta.continuous_fderiv (by simp)).norm
  obtain ⟨D0, hD0⟩ := (isCompact_closedBall (cs p) R).bddAbove_image hder.continuousOn
  let D := max D0 0
  have hD : 0 ≤ D := le_max_right _ _
  have hcut (z : LoopPlane) (hz : z ∈ O) : ‖fderiv ℝ eta z‖ ≤ D :=
    (hD0 ⟨z, Metric.ball_subset_closedBall hz, rfl⟩).trans (le_max_left _ _)
  have hbase : Continuous (fun z : LoopPlane => (16 : ℝ) / (‖z‖ ^ 2 + 4) ^ 2) :=
    continuous_const.div₀ (((continuous_norm.pow 2).add continuous_const).pow 2)
      (fun _ => by positivity)
  have hweightcont : Continuous (fun z : LoopPlane =>
      (16 / (‖z‖ ^ 2 + 4) ^ 2) ^ (1 - alpha)) :=
    hbase.rpow_const (fun _ => Or.inl (by positivity))
  obtain ⟨L, hL⟩ := (isCompact_closedBall (cs p) R).bddAbove_image hweightcont.continuousOn
  have hweight (z : LoopPlane) (hz : z ∈ O) :
      (16 / (‖z‖ ^ 2 + 4) ^ 2) ^ (1 - alpha) ≤ L :=
    hL ⟨z, Metric.ball_subset_closedBall hz, rfl⟩
  let T := fun s : ℝ => (1 + s / a) ^ alpha
  let S := fun s : ℝ => (1 + s) ^ (2 * alpha)
  let Q := fun s : ℝ => T s ^ 2 * S s
  let err := fun s : ℝ => 2 * T s * S s * s * (1 + 2 * C * D ^ 2) ^ alpha * L *
    (volume O).toReal
  have hT : Continuous T := (Real.continuous_rpow_const (by linarith : 0 ≤ alpha)).comp
    (continuous_const.add (continuous_id.div_const a))
  have hS : Continuous S := (Real.continuous_rpow_const (by linarith : 0 ≤ 2 * alpha)).comp
    (continuous_const.add continuous_id)
  have hQ : Continuous Q := (hT.pow 2).mul hS
  have herr : Continuous err := (((((continuous_const.mul hT).mul hS).mul continuous_id).mul
    continuous_const).mul continuous_const).mul continuous_const
  have hQ0 : Q 0 = 1 := by simp [Q, T, S]
  have herr0 : err 0 = 0 := by simp [err]
  intro eps heps
  have hsmall : ∀ᶠ s in 𝓝 (0 : ℝ), Q s * (2 * m) - 2 * m + err s < c0 * eps / 2 := by
    have h : ContinuousAt (fun s => Q s * (2 * m) - 2 * m + err s) 0 :=
      (((hQ.mul continuous_const).sub continuous_const).add herr).continuousAt
    have hval : Q 0 * (2 * m) - 2 * m + err 0 = 0 := by rw [hQ0, herr0]; ring
    exact h (gt_mem_nhds (by
      change Q 0 * (2 * m) - 2 * m + err 0 < c0 * eps / 2
      rw [hval]
      positivity))
  obtain ⟨s, hsmem, hsmall⟩ := ((eventually_mem_nhdsWithin : ∀ᶠ s : ℝ in 𝓝[>] 0, s ∈ Ioi 0).and
    (hsmall.filter_mono nhdsWithin_le_nhds)).exists
  have hs : 0 < s := hsmem
  obtain ⟨delta0, hdelta0, hmetricclose⟩ := (Metric.uniformContinuousOn_iff
    (α := EuclideanSpace ℝ (Fin n))
    (β := EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)).mp hmetriccont
    (s / 2) (by positivity)
  let delta := delta0 / 2
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hosc (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ K) (w : EuclideanSpace ℝ (Fin n))
      (hw : w ∈ K) (hdist : ‖y - w‖ ≤ delta) :
      ‖g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm y -
        g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm w‖ ≤ s / 2 := by
    have hh : dist y w < delta0 := by rw [dist_eq_norm]; dsimp [delta] at hdist; linarith
    exact (dist_eq_norm (g.pullbackCoefficients
      (chartAt (EuclideanSpace ℝ (Fin n)) b).symm y)
      (g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm w)) ▸
        (hmetricclose y hy w hw hh).le
  have huclose := Metric.tendstoUniformly_iff.mp hlim (min s delta / 2) (by positivity)
  have henergyclose : ∀ᶠ j in atTop,
      Q s * m60SphereAlphaEnergy g alpha (f j) < Q s * m + c0 * eps / 4 :=
    (henergy.const_mul (Q s)) (gt_mem_nhds (by
      have : 0 < c0 * eps / 4 := by positivity
      linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hcoord.and (huclose.and henergyclose))
  refine ⟨N, fun j hj k hk => ?_⟩
  have hclose (z : LoopPlane) (_ : z ∈ O) :
      ‖e (f j (cs.symm z)) - e (f k (cs.symm z))‖ ≤ min s delta := by
    have hdist := dist_triangle (e (f j (cs.symm z))) (u0 z) (e (f k (cs.symm z)))
    have hjz := (hN j hj).2.1 z
    have hkz := (hN k hk).2.1 z
    simp only [Function.comp_apply] at hjz hkz
    rw [dist_comm (e (f j (cs.symm z))) (u0 z)] at hdist
    rw [dist_eq_norm] at hdist
    exact hdist.trans (by linarith)
  have hi := suAlpha_local_pair_integral g ha ha0 hC hD hs.le hs p b rho hrho hrange hsupp
    e he (f j) (f k) (hf j) (hf k) (hn j) (hn k) hK hKt (hN j hj).1 (hN k hk).1
      hmetric hnorm hosc hclose hcut hweight
  change c0 * _ ≤ Q s * (_ + _) - 2 * m + err s at hi
  have hupper : Q s * (m60SphereAlphaEnergy g alpha (f j) +
      m60SphereAlphaEnergy g alpha (f k)) - 2 * m + err s < c0 * eps := by
    have hjE := (hN j hj).2.2
    have hkE := (hN k hk).2.2
    nlinarith only [hjE, hkE, hsmall]
  exact (mul_le_mul_iff_right₀ hc0).mp (hi.trans hupper.le)

set_option maxHeartbeats 1000000 in




theorem suAlpha_minimizing_local_cauchy [CompactSpace M] [T2Space M]
    (g : RiemannianMetric n M) {alpha : ℝ} (ha : 1 ≤ alpha)
    (f : ℕ → UnitTwoSphere → M) (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) ∞ (f j))
    (hn : ∀ j, ¬ IsNullHomotopicSphere (f j))
    (henergy : Tendsto (fun j => m60SphereAlphaEnergy g alpha (f j)) atTop
      (𝓝 (sInf (m60NonNullAlphaEnergyValues g alpha))))
    (f0 : C(UnitTwoSphere, M))
    (hlim : Tendsto (fun j => (⟨f j, (hf j).continuous⟩ : C(UnitTwoSphere, M)))
      atTop (𝓝 f0)) (p : UnitTwoSphere) :
    let c := chartAt (EuclideanSpace ℝ (Fin n)) (f0 p)
    let cs := chartAt LoopPlane p
    ∃ (e : M → EuclideanSpace ℝ (Fin n)) (r r0 : ℝ),
      ContMDiff (𝓡 n) (𝓡 n) ∞ e ∧ 0 < r ∧ 0 < r0 ∧
      Metric.closedBall (c (f0 p)) r0 ⊆ c.target ∧
      (∀ z ∈ Metric.closedBall (cs p) r,
        f0 (cs.symm z) ∈ c.source ∧ e (f0 (cs.symm z)) = c (f0 (cs.symm z)) ∧
          e (f0 (cs.symm z)) ∈ Metric.ball (c (f0 p)) r0) ∧
      (∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (cs p) r,
        f j (cs.symm z) ∈ c.source ∧ e =ᶠ[𝓝 (f j (cs.symm z))] c ∧
          e (f j (cs.symm z)) ∈ Metric.ball (c (f0 p)) r0) ∧
      ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N,
        (∫ z in Metric.ball (cs p) r,
          ‖suAlphaDerivativePair (e ∘ f j ∘ cs.symm) z -
            suAlphaDerivativePair (e ∘ f k ∘ cs.symm) z‖ ^ (2 * alpha)) ≤ eps := by
  let : UniformSpace M := uniformSpaceOfCompactR1
  let c := chartAt (EuclideanSpace ℝ (Fin n)) (f0 p)
  let cs := chartAt LoopPlane p
  obtain ⟨e, r0, R, he, hr0, hR, hKt, hlocal, htail⟩ :=
    suAlpha_common_chart_patch (n := n) (fun j => ⟨f j, (hf j).continuous⟩) f0 hlim p
  let K := Metric.closedBall (c (f0 p)) r0
  obtain ⟨a, C, ha0, hC, hBcont, hBnorm, hB⟩ := suAlpha_coordinate_metric_bounds g (f0 p)
    (K := K) (isCompact_closedBall _ _) (by
      intro y hy
      rw [extChartAt_target]
      exact ⟨hKt hy, ⟨y, rfl⟩⟩)
  let U : Set UnitTwoSphere := cs.source ∩ cs ⁻¹' Metric.ball (cs p) R
  have hU : IsOpen U := cs.isOpen_inter_preimage Metric.isOpen_ball
  have hpU : p ∈ U := by
    change p ∈ cs.source ∧ cs p ∈ Metric.ball (cs p) R
    exact ⟨mem_chart_source LoopPlane p, Metric.mem_ball_self hR⟩
  obtain ⟨b, _, hbsupp⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 2) p).mem_iff.mp
    (hU.mem_nhds hpU)
  let rho := fun x : UnitTwoSphere => b x / 2
  have hrho : ContMDiff (𝓡 2) 𝓘(ℝ) ∞ rho := b.contMDiff.div_const 2
  have hrange (x : UnitTwoSphere) : rho x ∈ Icc 0 (1 / 2) := by
    dsimp only [rho]
    exact ⟨div_nonneg b.nonneg (by norm_num), div_le_div_of_nonneg_right b.le_one (by norm_num)⟩
  have hsupp : tsupport rho ⊆ U := by
    have hsub : tsupport rho ⊆ tsupport (fun x => b x) :=
      tsupport_mul_subset_left (f := fun x => b x) (g := fun _ => (2 : ℝ)⁻¹)
    exact hsub.trans hbsupp
  have hcs : Continuous cs.symm := (suSphereChart_smooth p).continuous
  have hone : ∀ᶠ z in 𝓝 (cs p), rho (cs.symm z) = 1 / 2 := by
    have ht : Tendsto cs.symm (𝓝 (cs p)) (𝓝 p) := by
      have ht := hcs.tendsto (cs p)
      rw [cs.left_inv (mem_chart_source LoopPlane p)] at ht
      exact ht
    have hb := b.eventuallyEq_one.comp_tendsto
      ht
    filter_upwards [hb] with z hz
    change b (cs.symm z) = 1 at hz
    dsimp only [rho]
    rw [hz]
  obtain ⟨r1, hr1, hr1ball⟩ := Metric.mem_nhds_iff.mp hone
  let r := min R r1 / 2
  have hr : 0 < r := half_pos (lt_min hR hr1)
  have hrR : r < R := by have := min_le_left R r1; dsimp [r]; linarith [lt_min hR hr1]
  have hrr1 : r < r1 := by have := min_le_right R r1; dsimp [r]; linarith [lt_min hR hr1]
  have hinc : Metric.closedBall (cs p) r ⊆ Metric.closedBall (cs p) R :=
    Metric.closedBall_subset_closedBall hrR.le
  have hcoord : ∀ᶠ j in atTop, ∀ x ∈ U,
      f j x ∈ c.source ∧ e (f j x) = c (f j x) ∧ e (f j x) ∈ K := by
    filter_upwards [htail] with j hj x hx
    have h := hj (cs x) (Metric.ball_subset_closedBall hx.2)
    rw [cs.left_inv hx.1] at h
    exact ⟨h.1, h.2.2.self_of_nhds,
      h.2.2.self_of_nhds.symm ▸ Metric.ball_subset_closedBall h.2.1⟩
  have hfU : TendstoUniformly f f0 atTop := tendstoUniformlyOn_univ.mp
    (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hlim univ isCompact_univ)
  have heU := (CompactSpace.uniformContinuous_of_continuous he.continuous).comp_tendstoUniformly hfU
  have hweighted := suAlpha_minimizing_weighted_cauchy g ha ha0 hC p (f0 p) e he f hf hn
    henergy (e ∘ f0 ∘ cs.symm) (heU.comp cs.symm) rho hrho hrange hsupp
      (convex_closedBall _ _) hKt hcoord hB hBnorm hBcont
  refine ⟨e, r, r0, he, hr, hr0, hKt, ?_, ?_, ?_⟩
  · intro z hz
    have hh := hlocal z (hinc hz)
    exact ⟨hh.1, hh.2.2.self_of_nhds, hh.2.2.self_of_nhds.symm ▸ hh.2.1⟩
  · filter_upwards [htail] with j hj z hz
    have hh := hj z (hinc hz)
    exact ⟨hh.1, hh.2.2, hh.2.2.self_of_nhds.symm ▸ hh.2.1⟩
  intro eps heps
  obtain ⟨N, hN⟩ := hweighted (eps / 2) (half_pos heps)
  refine ⟨N, fun j hj k hk => ?_⟩
  let gap := fun z => ‖suAlphaDerivativePair (e ∘ f j ∘ cs.symm) z -
    suAlphaDerivativePair (e ∘ f k ∘ cs.symm) z‖ ^ (2 * alpha)
  have hu (l : ℕ) : ContDiff ℝ ∞ (e ∘ f l ∘ cs.symm) :=
    contMDiff_iff_contDiff.mp (he.comp ((hf l).comp (suSphereChart_smooth p)))
  have hgcont : Continuous gap := by
    apply (Real.continuous_rpow_const (by linarith : 0 ≤ 2 * alpha)).comp
    apply Continuous.norm
    apply Continuous.sub
    all_goals
      apply Continuous.prodMk
      all_goals
        exact ((hu _).continuous_fderiv (by simp)).clm_apply continuous_const
  have hg : IntegrableOn gap (Metric.ball (cs p) r) :=
    (hgcont.continuousOn.integrableOn_compact (isCompact_closedBall _ _)).mono_set
      Metric.ball_subset_closedBall
  have hwcont : Continuous (fun z => rho (cs.symm z) * gap z) :=
    (hrho.continuous.comp hcs).mul hgcont
  have hw : IntegrableOn (fun z => rho (cs.symm z) * gap z) (Metric.ball (cs p) R) :=
    (hwcont.continuousOn.integrableOn_compact (isCompact_closedBall _ _)).mono_set
      Metric.ball_subset_closedBall
  have heq : (1 / 2 : ℝ) * (∫ z in Metric.ball (cs p) r, gap z) =
      ∫ z in Metric.ball (cs p) r, rho (cs.symm z) * gap z := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
    rw [hr1ball ((Metric.mem_ball.mp hz).trans hrr1)]
  have hi := setIntegral_mono_set (s := Metric.ball (cs p) r) hw
    (Eventually.of_forall fun z => mul_nonneg (hrange _).1 (Real.rpow_nonneg (norm_nonneg _) _))
    (Eventually.of_forall (Metric.ball_subset_ball hrR.le))
  rw [← heq] at hi
  have hb := hN j hj k hk
  change (∫ z in Metric.ball (cs p) R, rho (cs.symm z) * gap z) ≤ eps / 2 at hb
  change (∫ z in Metric.ball (cs p) r, gap z) ≤ eps
  linarith



theorem suAlpha_minimizing_strong_derivatives [CompactSpace M] [T2Space M]
    (g : RiemannianMetric n M) {alpha C : ℝ} (ha : 1 ≤ alpha)
    (f : ℕ → UnitTwoSphere → M) (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) ∞ (f j))
    (hn : ∀ j, ¬ IsNullHomotopicSphere (f j))
    (hbound : ∀ j, m60SphereAlphaEnergy g alpha (f j) ≤ C)
    (henergy : Tendsto (fun j => m60SphereAlphaEnergy g alpha (f j)) atTop
      (𝓝 (sInf (m60NonNullAlphaEnergyValues g alpha))))
    (f0 : C(UnitTwoSphere, M))
    (hlim : Tendsto (fun j => (⟨f j, (hf j).continuous⟩ : C(UnitTwoSphere, M)))
      atTop (𝓝 f0)) (p : UnitTwoSphere) :
    let c := chartAt (EuclideanSpace ℝ (Fin n)) (f0 p)
    let cs := chartAt LoopPlane p
    ∃ (e : M → EuclideanSpace ℝ (Fin n)) (r r0 : ℝ) (k : ℕ → ℕ),
      ContMDiff (𝓡 n) (𝓡 n) ∞ e ∧ 0 < r ∧ 0 < r0 ∧ StrictMono k ∧
      Metric.closedBall (c (f0 p)) r0 ⊆ c.target ∧
      (∀ z ∈ Metric.closedBall (cs p) r,
        f0 (cs.symm z) ∈ c.source ∧ e (f0 (cs.symm z)) = c (f0 (cs.symm z)) ∧
          e (f0 (cs.symm z)) ∈ Metric.ball (c (f0 p)) r0) ∧
      (∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (cs p) r,
        f j (cs.symm z) ∈ c.source ∧ e =ᶠ[𝓝 (f j (cs.symm z))] c ∧
          e (f j (cs.symm z)) ∈ Metric.ball (c (f0 p)) r0) ∧
      ∃ V : Fin 2 → Lp (EuclideanSpace ℝ (Fin n)) 2
          (volume.restrict (Metric.ball (cs p) r)),
        (∀ i, MemLp (fun z => V i z) (ENNReal.ofReal (2 * alpha))
          (volume.restrict (Metric.ball (cs p) r))) ∧
        (∀ i (phi : LoopPlane → ℝ), ContDiff ℝ ∞ phi → HasCompactSupport phi →
          tsupport phi ⊆ Metric.ball (cs p) r →
          (∫ z in Metric.ball (cs p) r, phi z • V i z) =
            -(∫ z in Metric.ball (cs p) r,
              fderiv ℝ phi z (EuclideanSpace.basisFun (Fin 2) ℝ i) • c (f0 (cs.symm z)))) ∧
        ∀ i, Tendsto (fun j => eLpNorm (fun z =>
            fderiv ℝ (e ∘ f j ∘ cs.symm) z (EuclideanSpace.basisFun (Fin 2) ℝ i) - V i z)
          (ENNReal.ofReal (2 * alpha)) (volume.restrict (Metric.ball (cs p) r))) atTop (𝓝 0) := by
  let c := chartAt (EuclideanSpace ℝ (Fin n)) (f0 p)
  let cs := chartAt LoopPlane p
  obtain ⟨e, r, r0, he, hr, hr0, hKt, hlocal, htail, hcauchy⟩ :=
    suAlpha_minimizing_local_cauchy g ha f hf hn henergy f0 hlim p
  obtain ⟨V, k, hd, hk, hweak, hVp, htest⟩ :=
    suAlpha_observed_weak_derivatives g ha f hf hbound f0 hlim e he p r
  let mu := volume.restrict (Metric.ball (cs p) r)
  let u := fun j => e ∘ f j ∘ cs.symm
  have hu (j : ℕ) : ContDiff ℝ ∞ (u j) :=
    contMDiff_iff_contDiff.mp (he.comp ((hf j).comp (suSphereChart_smooth p)))
  let W := fun j i => (hd j i).toLp (fun z =>
    fderiv ℝ (u j) z (EuclideanSpace.basisFun (Fin 2) ℝ i))
  refine ⟨e, r, r0, k, he, hr, hr0, hk, hKt, hlocal, htail, V, hVp, ?_, ?_⟩
  · intro i phi hphi hc hsub
    rw [htest i phi hphi hc hsub]
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
    change _ • e (f0 (cs.symm z)) = _
    rw [(hlocal z (Metric.ball_subset_closedBall hz)).2.1]
  · intro i
    have hp : 1 ≤ 2 * alpha := by linarith
    have hcau : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ j ≥ N, ∀ l ≥ N,
        (∫⁻ z, ENNReal.ofReal (‖(W j i - W l i) z‖ ^ (2 * alpha)) ∂mu) ≤
          ENNReal.ofReal eps := by
      intro eps heps
      obtain ⟨N, hN⟩ := hcauchy eps heps
      refine ⟨N, fun j hj l hl => ?_⟩
      let gap := fun z => ‖suAlphaDerivativePair (u j) z -
        suAlphaDerivativePair (u l) z‖ ^ (2 * alpha)
      have hgapcont : Continuous gap := by
        apply (Real.continuous_rpow_const (by linarith : 0 ≤ 2 * alpha)).comp
        apply Continuous.norm
        apply Continuous.sub
        all_goals
          apply Continuous.prodMk
          all_goals exact ((hu _).continuous_fderiv (by simp)).clm_apply continuous_const
      have hg : Integrable gap mu :=
        (hgapcont.continuousOn.integrableOn_compact (isCompact_closedBall _ _)).mono_set
          Metric.ball_subset_closedBall
      have hcol (z : LoopPlane) :
          ‖fderiv ℝ (u j) z (EuclideanSpace.basisFun (Fin 2) ℝ i) -
            fderiv ℝ (u l) z (EuclideanSpace.basisFun (Fin 2) ℝ i)‖ ≤
          ‖suAlphaDerivativePair (u j) z - suAlphaDerivativePair (u l) z‖ := by
        fin_cases i
        · exact norm_fst_le (suAlphaDerivativePair (u j) z - suAlphaDerivativePair (u l) z)
        · exact norm_snd_le (suAlphaDerivativePair (u j) z - suAlphaDerivativePair (u l) z)
      calc
        _ ≤ ∫⁻ z, ENNReal.ofReal (gap z) ∂mu := by
          apply lintegral_mono_ae
          filter_upwards [Lp.coeFn_sub (W j i) (W l i),
            (hd j i).coeFn_toLp, (hd l i).coeFn_toLp] with z hsub hjz hlz
          rw [hsub]
          change ENNReal.ofReal (‖W j i z - W l i z‖ ^ (2 * alpha)) ≤ _
          rw [hjz, hlz]
          exact ENNReal.ofReal_le_ofReal
            (Real.rpow_le_rpow (norm_nonneg _) (hcol z) (by linarith))
        _ = ENNReal.ofReal (∫ z, gap z ∂mu) :=
          (ofReal_integral_eq_lintegral_ofReal hg
            (Eventually.of_forall fun z => Real.rpow_nonneg (norm_nonneg _) _)).symm
        _ ≤ ENNReal.ofReal eps := ENNReal.ofReal_le_ofReal
          (hN j hj l hl)
    have hstrong := suStrongLp_of_subseq_weak_and_power_cauchy
      (u := fun j => W j i) (v := V i) hp hk (hweak i) hcau
    have heq (j : ℕ) : eLpNorm (fun z =>
        fderiv ℝ (u j) z (EuclideanSpace.basisFun (Fin 2) ℝ i) - V i z)
        (ENNReal.ofReal (2 * alpha)) mu =
        eLpNorm (fun z => (W j i - V i) z) (ENNReal.ofReal (2 * alpha)) mu := by
      apply eLpNorm_congr_ae
      filter_upwards [Lp.coeFn_sub (W j i) (V i), (hd j i).coeFn_toLp] with z hsub hj
      rw [hsub]
      change _ = W j i z - V i z
      rw [hj]
    change Tendsto (fun j => eLpNorm (fun z =>
      fderiv ℝ (u j) z (EuclideanSpace.basisFun (Fin 2) ℝ i) - V i z)
      (ENNReal.ofReal (2 * alpha)) mu) atTop (𝓝 0)
    simp_rw [heq]
    exact hstrong

end PoincareConjecture.M60

namespace PoincareConjecture.M60

section NonlinearIntegral

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  {mu : Measure X} {p : ℝ}



theorem suAlpha_power_uniformIntegrable {f : ℕ → X → E} (hp : 0 < p)
    (hf : UnifIntegrable f (ENNReal.ofReal p) mu) :
    UnifIntegrable (fun j x => ‖f j x‖ ^ p) 1 mu := by
  intro eps heps
  obtain ⟨d, hd, hsmall⟩ := hf (Real.rpow_pos_of_pos heps p⁻¹)
  refine ⟨d, hd, fun j s hs hmu => ?_⟩
  have heq : s.indicator (fun x => ‖f j x‖ ^ p) =
      fun x => ‖s.indicator (f j) x‖ ^ p := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx, Real.zero_rpow hp.ne']
  rw [heq, eLpNorm_norm_rpow _ hp, one_mul]
  have hb := ENNReal.rpow_le_rpow (hsmall j s hs hmu) hp.le
  rw [ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos heps _),
    Real.rpow_inv_rpow heps.le hp.ne'] at hb
  exact hb



theorem suAlpha_uniformIntegrable_dominated {f g : ℕ → X → ℝ}
    {C : ℝ} (hC : 0 < C) (hg : UnifIntegrable g 1 mu)
    (hfg : ∀ j, ∀ᵐ x ∂mu, ‖f j x‖ ≤ C * ‖g j x‖) : UnifIntegrable f 1 mu := by
  intro eps heps
  obtain ⟨d, hd, hsmall⟩ := hg (div_pos heps hC)
  refine ⟨d, hd, fun j s hs hmu => ?_⟩
  have hb : eLpNorm (s.indicator (f j)) 1 mu ≤
      ENNReal.ofReal C * eLpNorm (s.indicator (g j)) 1 mu := by
    calc
      _ ≤ eLpNorm (fun x => C * s.indicator (g j) x) 1 mu := eLpNorm_mono_ae (by
        filter_upwards [hfg j] with x hx
        by_cases hxs : x ∈ s
        · simpa [hxs, norm_mul, Real.norm_of_nonneg hC.le] using hx
        · simp [hxs])
      _ = _ := by
        change eLpNorm (C • s.indicator (g j)) 1 mu = _
        rw [eLpNorm_const_smul, Real.enorm_of_nonneg hC.le]
  refine hb.trans ?_
  calc
    ENNReal.ofReal C * eLpNorm (s.indicator (g j)) 1 mu ≤
        ENNReal.ofReal C * ENNReal.ofReal (eps / C) := by
          gcongr
          exact hsmall j s hs hmu
    _ = ENNReal.ofReal eps := by rw [← ENNReal.ofReal_mul hC.le, mul_div_cancel₀ _ hC.ne']



theorem suAlpha_nonlinear_integral_limit [IsFiniteMeasure mu]
    {f : ℕ → X → E} {f0 : X → E} (hp : 1 ≤ p)
    (hf : ∀ j, MemLp (f j) (ENNReal.ofReal p) mu)
    (hf0 : MemLp f0 (ENNReal.ofReal p) mu)
    (hstrong : Tendsto (fun j => eLpNorm (f j - f0) (ENNReal.ofReal p) mu) atTop (𝓝 0))
    (F : X → E → ℝ)
    (hcont : ∀ᵐ x ∂mu, ContinuousAt (F x) (f0 x))
    (hF : ∀ j, AEStronglyMeasurable (fun x => F x (f j x)) mu)
    (hF0 : AEStronglyMeasurable (fun x => F x (f0 x)) mu)
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ j, ∀ᵐ x ∂mu, ‖F x (f j x)‖ ≤ C * (1 + ‖f j x‖ ^ p))
    (hbound0 : ∀ᵐ x ∂mu, ‖F x (f0 x)‖ ≤ C * (1 + ‖f0 x‖ ^ p)) :
    Integrable (fun x => F x (f0 x)) mu ∧
      Tendsto (fun j => ∫ x, F x (f j x) ∂mu) atTop (𝓝 (∫ x, F x (f0 x) ∂mu)) ∧
      Tendsto (fun j => eLpNorm (fun x => F x (f j x) - F x (f0 x)) 1 mu)
        atTop (𝓝 0) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hp' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  have hpne : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  have hpower (j : ℕ) : MemLp (fun x => ‖f j x‖ ^ p) 1 mu := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using
      (hf j).norm_rpow hpne ENNReal.ofReal_ne_top
  have hpower0 : MemLp (fun x => ‖f0 x‖ ^ p) 1 mu := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using
      hf0.norm_rpow hpne ENNReal.ofReal_ne_top
  have hbase : UnifIntegrable (fun j x => 1 + ‖f j x‖ ^ p) 1 mu :=
    (unifIntegrable_const (by rfl) ENNReal.one_ne_top (memLp_const (1 : ℝ))).add
      (suAlpha_power_uniformIntegrable hp0
        (unifIntegrable_of_tendsto_Lp hp' ENNReal.ofReal_ne_top hf hf0 hstrong))
      (by rfl) (fun _ => aestronglyMeasurable_const) (fun j => (hpower j).1)
  have hUI : UnifIntegrable (fun j x => F x (f j x)) 1 mu :=
    suAlpha_uniformIntegrable_dominated hC hbase (fun j => by
      filter_upwards [hbound j] with x hx
      simpa only [Real.norm_of_nonneg (by positivity : 0 ≤ 1 + ‖f j x‖ ^ p)] using hx)
  have hlimLp : MemLp (fun x => F x (f0 x)) 1 mu :=
    ((memLp_const (1 : ℝ)).add hpower0).const_mul C |>.of_le hF0 (by
      filter_upwards [hbound0] with x hx
      simpa only [Pi.add_apply, Real.norm_of_nonneg
        (by positivity : 0 ≤ C * (1 + ‖f0 x‖ ^ p))] using hx)
  have hL1 : Tendsto (fun j => eLpNorm (fun x => F x (f j x) - F x (f0 x)) 1 mu)
      atTop (𝓝 0) := by
    apply tendsto_of_subseq_tendsto
    intro ns hns
    have hmeasure := tendstoInMeasure_of_tendsto_eLpNorm hpne
      (fun j => (hf (ns j)).1) hf0.1 (hstrong.comp hns)
    obtain ⟨ms, _, hpoint⟩ := hmeasure.exists_seq_tendsto_ae
    have hpointF : ∀ᵐ x ∂mu, Tendsto (fun j => F x (f (ns (ms j)) x)) atTop
        (𝓝 (F x (f0 x))) := by
      filter_upwards [hpoint, hcont] with x hx hc
      exact hc.tendsto.comp hx
    have hUI' : UnifIntegrable (fun j x => F x (f (ns (ms j)) x)) 1 mu := by
      intro eps heps
      obtain ⟨d, hd, hh⟩ := hUI heps
      exact ⟨d, hd, fun j => hh (ns (ms j))⟩
    exact ⟨ms, tendsto_Lp_finite_of_tendsto_ae (by rfl) ENNReal.one_ne_top
      (fun j => hF (ns (ms j))) hlimLp hUI' hpointF⟩
  refine ⟨memLp_one_iff_integrable.mp hlimLp,
    tendsto_integral_of_L1' _ hF0 (Eventually.of_forall fun j => ?_) hL1, hL1⟩
  exact memLp_one_iff_integrable.mp
    (((memLp_const (1 : ℝ)).add (hpower j)).const_mul C |>.of_le (hF j) (by
      filter_upwards [hbound j] with x hx
      simpa only [Pi.add_apply, Real.norm_of_nonneg
        (by positivity : 0 ≤ C * (1 + ‖f j x‖ ^ p))] using hx))

end NonlinearIntegral



theorem suAlpha_density_growth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) {alpha c C L : ℝ} (ha : 0 ≤ alpha)
    (hc : c ∈ Icc 0 1) (hC : 0 ≤ C) (hn : ‖B‖ ≤ C)
    (hpos : ∀ v, 0 ≤ B v v) (_hL : 0 ≤ L) (hweight : c ^ (1 - alpha) ≤ L) (v : E) :
    ‖c ^ (1 - alpha) * suRegularizedQuadratic B c alpha v‖ ≤
      L * (1 + C) ^ alpha * (1 + ‖v‖ ^ (2 * alpha)) := by
  have hquad : B v v ≤ C * ‖v‖ ^ 2 := by
    have hb := B.le_opNorm₂ v v
    rw [Real.norm_of_nonneg (hpos v)] at hb
    have hnorm := mul_le_mul_of_nonneg_right hn (sq_nonneg ‖v‖)
    nlinarith
  have hbase : 0 ≤ c + B v v := add_nonneg hc.1 (hpos v)
  have hpow : (c + B v v) ^ alpha ≤
      (1 + C) ^ alpha * (1 + ‖v‖ ^ (2 * alpha)) := by
    by_cases hv : ‖v‖ ≤ 1
    · have hq : c + B v v ≤ 1 + C := by
        have hsq : ‖v‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg v]
        nlinarith [mul_le_mul_of_nonneg_left hsq hC, hc.2]
      have hb := Real.rpow_le_rpow hbase hq ha
      have hr : 0 ≤ ‖v‖ ^ (2 * alpha) := Real.rpow_nonneg (norm_nonneg _) _
      nlinarith [Real.rpow_nonneg (by linarith : 0 ≤ 1 + C) alpha]
    · have hv1 : 1 ≤ ‖v‖ ^ 2 := by nlinarith [norm_nonneg v]
      have hq : c + B v v ≤ (1 + C) * ‖v‖ ^ 2 := by nlinarith [hc.2]
      have hb := Real.rpow_le_rpow hbase hq ha
      rw [Real.mul_rpow (by linarith) (sq_nonneg _),
        ← Real.rpow_two ‖v‖, ← Real.rpow_mul (norm_nonneg _)] at hb
      nlinarith [Real.rpow_nonneg (by linarith : 0 ≤ 1 + C) alpha]
  dsimp only [suRegularizedQuadratic]
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hc.1 _)
    (Real.rpow_nonneg hbase _))]
  calc
    _ ≤ c ^ (1 - alpha) * ((1 + C) ^ alpha * (1 + ‖v‖ ^ (2 * alpha))) :=
      mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hc.1 _)
    _ ≤ L * ((1 + C) ^ alpha * (1 + ‖v‖ ^ (2 * alpha))) :=
      mul_le_mul_of_nonneg_right hweight (by positivity)
    _ = _ := by ring

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem suAlpha_chart_integral_limit
    (g : RiemannianMetric n M) {alpha R : ℝ} (ha : 1 ≤ alpha)
    (p : UnitTwoSphere) (b : M)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt (𝓡 n) b).target)
    (W : ℕ → LoopPlane → EuclideanSpace ℝ (Fin n) ×
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (W0 : LoopPlane → EuclideanSpace ℝ (Fin n) ×
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (hW : ∀ j, MemLp (W j) (ENNReal.ofReal (2 * alpha))
      (volume.restrict (Metric.ball ((chartAt LoopPlane p) p) R)))
    (hW0 : MemLp W0 (ENNReal.ofReal (2 * alpha))
      (volume.restrict (Metric.ball ((chartAt LoopPlane p) p) R)))
    (hstrong : Tendsto (fun j => eLpNorm (W j - W0) (ENNReal.ofReal (2 * alpha))
      (volume.restrict (Metric.ball ((chartAt LoopPlane p) p) R))) atTop (𝓝 0))
    (hvalues : ∀ j, ∀ᵐ z ∂volume.restrict (Metric.ball ((chartAt LoopPlane p) p) R),
      (W j z).1 ∈ K)
    (hvalues0 : ∀ᵐ z ∂volume.restrict (Metric.ball ((chartAt LoopPlane p) p) R),
      (W0 z).1 ∈ K) :
    let lambda := fun z : LoopPlane => 16 / (‖z‖ ^ 2 + 4) ^ 2
    let B := fun y => suAlphaPairMetric (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm y)
    let F := fun z (w : EuclideanSpace ℝ (Fin n) ×
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) =>
      lambda z ^ (1 - alpha) * suRegularizedQuadratic (B w.1) (lambda z) alpha w.2
    (∀ j, IntegrableOn (fun z => F z (W j z)) (Metric.ball ((chartAt LoopPlane p) p) R)) ∧
    IntegrableOn (fun z => F z (W0 z)) (Metric.ball ((chartAt LoopPlane p) p) R) ∧
      Tendsto (fun j => ∫ z in Metric.ball ((chartAt LoopPlane p) p) R, F z (W j z)) atTop
        (𝓝 (∫ z in Metric.ball ((chartAt LoopPlane p) p) R, F z (W0 z))) ∧
      Tendsto (fun j => eLpNorm (fun z => F z (W j z) - F z (W0 z)) 1
        (volume.restrict (Metric.ball ((chartAt LoopPlane p) p) R))) atTop (𝓝 0) := by
  classical
  let mu := volume.restrict (Metric.ball ((chartAt LoopPlane p) p) R)
  let : IsFiniteMeasure mu := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let lambda := fun z : LoopPlane => 16 / (‖z‖ ^ 2 + 4) ^ 2
  let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
  let B := fun y => suAlphaPairMetric (G y)
  let F := fun z (w : EuclideanSpace ℝ (Fin n) ×
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) =>
    lambda z ^ (1 - alpha) * suRegularizedQuadratic (B w.1) (lambda z) alpha w.2
  have hlam : Continuous lambda := continuous_const.div₀
    (((continuous_norm.pow 2).add continuous_const).pow 2) (fun _ => by positivity)
  have hlam0 (z : LoopPlane) : 0 < lambda z := by dsimp [lambda]; positivity
  have hlam1 (z : LoopPlane) : lambda z ≤ 1 := by
    dsimp only [lambda]
    apply (div_le_one (by positivity)).mpr
    nlinarith [sq_nonneg ‖z‖]
  have hwcont : Continuous (fun z => lambda z ^ (1 - alpha)) :=
    hlam.rpow_const (fun z => Or.inl (hlam0 z).ne')
  obtain ⟨L0, hL0⟩ := (isCompact_closedBall ((chartAt LoopPlane p) p) R).bddAbove_image
    hwcont.continuousOn
  let L := max L0 1
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hweight (z : LoopPlane) (hz : z ∈ Metric.ball ((chartAt LoopPlane p) p) R) :
      lambda z ^ (1 - alpha) ≤ L :=
    (hL0 ⟨z, Metric.ball_subset_closedBall hz, rfl⟩).trans (le_max_left _ _)
  obtain ⟨a, C, ha0, hC, _, hGn, hGa⟩ := suAlpha_coordinate_metric_bounds g b hK hKt
  have hBn (y) (hy : y ∈ K) : ‖B y‖ ≤ 2 * C :=
    (suAlphaPairMetric_norm _).trans (by nlinarith [hGn y hy])
  have hBp (y) (hy : y ∈ K) (v) : 0 ≤ B y v v :=
    (mul_nonneg ha0.le (sq_nonneg _)).trans (suAlphaPairMetric_coercive _ ha0.le (hGa y hy) v)
  have hBc : ContinuousOn B K :=
    suAlphaPairMetric_continuous.comp_continuousOn
      ((g.contDiffOn_chartCoefficients b).continuousOn.mono hKt)
  let : MeasurableSpace
      ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) := borel _
  let : BorelSpace
      ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) := ⟨rfl⟩
  let Bext := K.piecewise B (fun _ => 0)
  have hBext : Measurable Bext := hBc.measurable_piecewise continuous_const.continuousOn
    hK.measurableSet
  have hmeas (w : LoopPlane → EuclideanSpace ℝ (Fin n) ×
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
      (hw : AEStronglyMeasurable w mu) (hval : ∀ᵐ z ∂mu, (w z).1 ∈ K) :
      AEStronglyMeasurable (fun z => F z (w z)) mu := by
    have hBm : AEStronglyMeasurable (fun z => Bext (w z).1) mu :=
      (hBext.comp_aemeasurable hw.fst.aemeasurable).aestronglyMeasurable
    have hquad : AEStronglyMeasurable (fun z => Bext (w z).1 (w z).2 (w z).2) mu :=
      ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        (((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
          (hBm.prodMk hw.snd)).prodMk hw.snd))
    have hh := hwcont.aestronglyMeasurable.mul
      ((Real.continuous_rpow_const (by linarith : 0 ≤ alpha)).comp_aestronglyMeasurable
        (hlam.aestronglyMeasurable.add hquad))
    apply hh.congr
    filter_upwards [hval] with z hz
    simp only [Pi.mul_apply, Pi.add_apply, F, suRegularizedQuadratic, Bext,
      piecewise_eq_of_mem K B _ hz]
  have hcont : ∀ᵐ z ∂mu, ContinuousAt (F z) (W0 z) := by
    filter_upwards [hvalues0] with z hz
    have hG : ContinuousAt G (W0 z).1 :=
      ((g.contDiffOn_chartCoefficients b).contDiffAt
        ((isOpen_extChartAt_target b).mem_nhds (hKt hz))).continuousAt
    have hB : ContinuousAt (fun w : EuclideanSpace ℝ (Fin n) ×
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) => B w.1) (W0 z) :=
      suAlphaPairMetric_continuous.continuousAt.comp
        (hG.comp continuous_fst.continuousAt)
    exact continuousAt_const.mul
      ((Real.continuous_rpow_const (by linarith : 0 ≤ alpha)).continuousAt.comp
        (continuousAt_const.add ((hB.clm_apply continuous_snd.continuousAt).clm_apply
          continuous_snd.continuousAt)))
  have hgrowth (w : LoopPlane → EuclideanSpace ℝ (Fin n) ×
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
      (hval : ∀ᵐ z ∂mu, (w z).1 ∈ K) :
      ∀ᵐ z ∂mu, ‖F z (w z)‖ ≤ L * (1 + 2 * C) ^ alpha *
        (1 + ‖w z‖ ^ (2 * alpha)) := by
    filter_upwards [hval, ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz hzO
    exact (suAlpha_density_growth (B (w z).1) (by linarith)
      ⟨(hlam0 z).le, hlam1 z⟩ (by positivity) (hBn _ hz) (hBp _ hz) hL.le
        (hweight z hzO) (w z).2).trans (by
          gcongr
          exact norm_snd_le (w z))
  refine ⟨?_, suAlpha_nonlinear_integral_limit (by linarith : 1 ≤ 2 * alpha)
    hW hW0 hstrong F hcont (fun j => hmeas _ (hW j).1 (hvalues j))
      (hmeas _ hW0.1 hvalues0) (by positivity : 0 < L * (1 + 2 * C) ^ alpha)
        (fun j => hgrowth _ (hvalues j)) (hgrowth _ hvalues0)⟩
  intro j
  have hpower : Integrable (fun z => ‖W j z‖ ^ (2 * alpha)) mu := by
    simpa only [ENNReal.toReal_ofReal (by linarith : 0 ≤ 2 * alpha)] using
      (hW j).integrable_norm_rpow (by simp; linarith) ENNReal.ofReal_ne_top
  exact ((integrable_const (1 : ℝ)).add hpower).const_mul
    (L * (1 + 2 * C) ^ alpha) |>.mono' (hmeas _ (hW j).1 (hvalues j))
      (hgrowth _ (hvalues j))

end PoincareConjecture.M60
