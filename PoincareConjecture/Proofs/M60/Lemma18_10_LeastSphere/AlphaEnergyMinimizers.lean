import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.PalaisSmale
import PoincareConjecture.Proofs.M58.Mathlib.LocalContraction
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Geometry.Manifold.WhitneyEmbedding
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UniformSpace.OfCompactT2
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.WeakCompactness.StrongLimit
import PoincareConjecture.Proofs.M40.Mathlib.SupportedChartSmoothing
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.EnergyDensityCoordinates

import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUAlphaCoordinateCompactness
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUAlphaWeakCompactness
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalInterface
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUAlphaLocalComparison
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUAlphaStrongConvergence
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUAlphaFirstVariation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Uniformity
open scoped Manifold ContDiff Topology Bundle BoundedContinuousFunction ENNReal

noncomputable section

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

section Variational

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m60SphereAlphaEnergy_bounded_minimizing_sequences
    [T2Space M] [SecondCountableTopology M]
    (g : RiemannianMetric n M) (x : M)
    (hpi : Nontrivial (HomotopyGroup.Pi 2 M x)) :
    ∃ C : ℝ, 0 < C ∧ ∀ alpha : ℝ, 1 ≤ alpha → alpha ≤ 2 →
      ∃ f : ℕ → UnitTwoSphere → M,
        (∀ j, ContMDiff (𝓡 2) (𝓡 n) ∞ (f j)) ∧
        (∀ j, ¬ IsNullHomotopicSphere (f j)) ∧
        (∀ j, m60SphereAlphaEnergy g alpha (f j) < C) ∧
        Tendsto (fun j => m60SphereAlphaEnergy g alpha (f j)) atTop
          (𝓝 (sInf (m60NonNullAlphaEnergyValues g alpha))) := by
  obtain ⟨f0, hf0, hn0⟩ := m60_exists_smooth_nonNull_sphere_of_nontrivial_pi2 (n := n) x hpi
  obtain ⟨C, hC, hbound⟩ := m60SphereAlphaEnergy_uniform_competitor_bound g f0 hf0
  refine ⟨C, hC, fun alpha halpha htwo => ?_⟩
  obtain ⟨f, hf, hn, _, hlim⟩ := m60SphereAlphaEnergy_minimizing_sequence g alpha x hpi
  have hinf : sInf (m60NonNullAlphaEnergyValues g alpha) ≤ m60SphereAlphaEnergy g alpha f0 :=
    csInf_le (m60NonNullAlphaEnergyValues_bddBelow g alpha) ⟨f0, hf0, hn0, rfl⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hlim (gt_mem_nhds (hinf.trans_lt (hbound alpha halpha htwo))))
  exact ⟨fun j => f (j + N), fun j => hf _, fun j => hn _,
    fun j => hN _ (Nat.le_add_left _ _), hlim.comp (tendsto_add_atTop_nat N)⟩

end Variational

namespace M60

theorem eventually_homotopic_of_tendstoUniformly
    {n : ℕ} {M : Type u} [UniformSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [CompactSpace M] [T2Space M]
    {X : Type*} [TopologicalSpace X]
    (f : ℕ → C(X, M)) (f0 : C(X, M))
    (hlim : TendstoUniformly (fun j => (f j : X → M)) f0 atTop) :
    ∀ᶠ j in atTop, (f j).Homotopic f0 := by
  obtain ⟨C, U, hU, hdiag, h0, h1, _, hs⟩ :=
    Proofs.M58.exists_local_contraction (M := M) (𝓡 n) isCompact_univ 0
  have hUn : U ∈ 𝓤 M := by
    rw [← nhdsSet_diagonal_eq_uniformity]
    exact hU.mem_nhdsSet.mpr hdiag
  filter_upwards [hlim U hUn] with j hj
  refine ⟨{
    toFun := fun p => C ((p.1 : ℝ), f0 p.2, f j p.2)
    continuous_toFun := ?_
    map_zero_left := fun x => h0 _ _
    map_one_left := fun x => h1 _ (hj x)
  }⟩
  apply continuous_iff_continuousAt.mpr
  intro p
  exact (hs _ ⟨p.1.property, hj p.2⟩).continuousAt.comp
    ((continuous_subtype_val.comp continuous_fst).continuousAt.prodMk
      ((f0.continuous.comp continuous_snd).continuousAt.prodMk
        ((f j).continuous.comp continuous_snd).continuousAt))

end M60

theorem m60NonNullSphere_of_uniform_limit
    {n : ℕ} {M : Type u} [UniformSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [CompactSpace M] [T2Space M]
    (f : ℕ → C(UnitTwoSphere, M)) (f0 : C(UnitTwoSphere, M))
    (hn : ∀ j, ¬ IsNullHomotopicSphere (f j))
    (hlim : TendstoUniformly (fun j => (f j : UnitTwoSphere → M)) f0 atTop) :
    ¬ IsNullHomotopicSphere f0 := by
  obtain ⟨j, hj⟩ := (M60.eventually_homotopic_of_tendstoUniformly (n := n) f f0 hlim).exists
  rintro ⟨_, x, hx⟩
  exact hn j ⟨(f j).continuous, x, hj.trans hx⟩

theorem m60SphereAlphaEnergy_nonNull_subsequence
    [CompactSpace M] [T2Space M]
    (g : RiemannianMetric n M) {alpha C : ℝ} (ha : 1 < alpha)
    (f : ℕ → UnitTwoSphere → M) (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) ∞ (f j))
    (hn : ∀ j, ¬ IsNullHomotopicSphere (f j))
    (hbound : ∀ j, m60SphereAlphaEnergy g alpha (f j) ≤ C) :
    ∃ (f0 : C(UnitTwoSphere, M)) (k : ℕ → ℕ), StrictMono k ∧
      ¬ IsNullHomotopicSphere f0 ∧
      Tendsto (fun j => (⟨f (k j), (hf (k j)).continuous⟩ : C(UnitTwoSphere, M)))
        atTop (𝓝 f0) := by
  obtain ⟨d, e, he, hei, _⟩ := exists_embedding_euclidean_of_compact (I := 𝓡 n) (M := M)
  let : MetricSpace M := hei.isEmbedding.comapMetricSpace e
  have hi : Isometry e := fun _ _ => rfl
  have hequi : Equicontinuous f := hi.isUniformInducing.equicontinuous_iff.mpr
    (M60.suAlpha_embedding_equicontinuous g e he ha f hf hbound)
  let F : ℕ → UnitTwoSphere →ᵇ M := fun j =>
    BoundedContinuousFunction.mkOfCompact ⟨f j, (hf j).continuous⟩
  have hequi' : Equicontinuous ((↑) : range F → UnitTwoSphere → M) := by
    have heq : (fun v : range F => (fun p => F v.2.choose p)) =
        ((↑) : range F → UnitTwoSphere → M) := by
      funext v p
      exact congrArg (fun w : UnitTwoSphere →ᵇ M => w p) v.2.choose_spec
    rw [← heq]
    exact hequi.comp fun v : range F => v.2.choose
  have hc : IsCompact (closure (range F)) :=
    BoundedContinuousFunction.arzela_ascoli univ isCompact_univ (range F)
      (fun _ _ _ => mem_univ _) hequi'
  obtain ⟨v, _, k, hk, hlim⟩ := hc.tendsto_subseq
    (fun j => subset_closure (mem_range_self j))
  have hv := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlim
  refine ⟨v.toContinuousMap, k, hk, ?_, ?_⟩
  · exact m60NonNullSphere_of_uniform_limit (n := n)
      (fun j => ⟨f (k j), (hf (k j)).continuous⟩) v.toContinuousMap (fun j => hn (k j)) hv
  · exact ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mpr
      (fun _ _ => hv.tendstoUniformlyOn)

namespace M60

section LocalState

variable {X E F : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  [NormedAddCommGroup F] {mu : Measure X} {q : ℝ≥0∞}

private theorem memLp_pair {u : X → E} {v : X → F}
    (hu : MemLp u q mu) (hv : MemLp v q mu) : MemLp (fun z => (u z, v z)) q mu :=
  (hu.norm.add hv.norm).of_le (hu.1.prodMk hv.1) (Eventually.of_forall fun z => by
    simp only [Prod.norm_def, Pi.add_apply, Real.norm_of_nonneg (add_nonneg
      (norm_nonneg _) (norm_nonneg _))]
    exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _))

private theorem strong_pair {u : ℕ → X → E} {v : ℕ → X → F}
    {u0 : X → E} {v0 : X → F} (hq : 1 ≤ q)
    (hu : ∀ j, AEStronglyMeasurable (u j) mu) (hv : ∀ j, AEStronglyMeasurable (v j) mu)
    (hu0 : AEStronglyMeasurable u0 mu) (hv0 : AEStronglyMeasurable v0 mu)
    (hlu : Tendsto (fun j => eLpNorm (u j - u0) q mu) atTop (𝓝 0))
    (hlv : Tendsto (fun j => eLpNorm (v j - v0) q mu) atTop (𝓝 0)) :
    Tendsto (fun j => eLpNorm (fun z => (u j z, v j z) - (u0 z, v0 z)) q mu)
      atTop (𝓝 0) := by
  have hb (j : ℕ) : eLpNorm (fun z => (u j z, v j z) - (u0 z, v0 z)) q mu ≤
      eLpNorm (u j - u0) q mu + eLpNorm (v j - v0) q mu := by
    calc
      _ ≤ eLpNorm (fun z => ‖u j z - u0 z‖ + ‖v j z - v0 z‖) q mu :=
        eLpNorm_mono (fun z => by
          rw [Real.norm_of_nonneg (by positivity), Prod.norm_def]
          exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _))
      _ ≤ _ := by
        have hh := eLpNorm_add_le ((hu j).sub hu0).norm ((hv j).sub hv0).norm hq
        rw [eLpNorm_norm, eLpNorm_norm] at hh
        convert! hh using 1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [add_zero] using hlu.add hlv) (fun _ => bot_le) hb

private theorem strong_of_uniform [IsFiniteMeasure mu]
    {u : ℕ → X → E} {u0 : X → E}
    (hu : ∀ j, AEStronglyMeasurable (u j) mu) (hu0 : AEStronglyMeasurable u0 mu)
    (hlim : TendstoUniformly u u0 atTop) :
    Tendsto (fun j => eLpNorm (u j - u0) q mu) atTop (𝓝 0) := by
  have htop : Tendsto (fun j => eLpNorm (u j - u0) ∞ mu) atTop (𝓝 0) := by
    rw [ENNReal.tendsto_atTop_zero]
    intro eps heps
    by_cases ht : eps = ⊤
    · exact ⟨0, fun _ _ => by rw [ht]; exact le_top⟩
    have heps' : 0 < eps.toReal := ENNReal.toReal_pos heps.ne' ht
    obtain ⟨N, hN⟩ := eventually_atTop.mp (Metric.tendstoUniformly_iff.mp hlim eps.toReal heps')
    refine ⟨N, fun j hj => ?_⟩
    rw [eLpNorm_exponent_top]
    have hh := eLpNormEssSup_le_of_ae_bound (μ := mu)
      (Eventually.of_forall fun z => show ‖(u j - u0) z‖ ≤ eps.toReal from by
        rw [Pi.sub_apply, ← dist_eq_norm, dist_comm]
        exact (hN j hj z).le)
    simpa only [ENNReal.ofReal_toReal ht] using hh
  have hconst : mu univ ^ (1 / q.toReal) ≠ ⊤ := by finiteness
  have hm := (ENNReal.continuousAt_mul_const (b := 0) (Or.inl hconst)).tendsto.comp htop
  have hm' : Tendsto (fun j => eLpNorm (u j - u0) ∞ mu * mu univ ^ (1 / q.toReal))
      atTop (𝓝 0) := by simpa only [Function.comp_def, zero_mul] using hm
  have hb (j : ℕ) : eLpNorm (u j - u0) q mu ≤
      eLpNorm (u j - u0) ∞ mu * mu univ ^ (1 / q.toReal) := by
    simpa only [ENNReal.toReal_top, div_zero, sub_zero] using
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := q) (q := ∞) le_top ((hu j).sub hu0)
  have hz : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0) := tendsto_const_nhds
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hz hm' (fun _ => bot_le) hb

end LocalState

alias suAlpha_memLp_pair := memLp_pair
alias suAlpha_strong_pair := strong_pair
alias suAlpha_strong_of_uniform := strong_of_uniform

private theorem continuous_memLp_ball {E : Type*} [NormedAddCommGroup E]
    {v : LoopPlane → E} (hv : Continuous v) (c : LoopPlane) (r : ℝ) (q : ℝ≥0∞) :
    MemLp v q (volume.restrict (Metric.ball c r)) := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball c r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  obtain ⟨C, hC⟩ := (isCompact_closedBall c r).bddAbove_image hv.norm.continuousOn
  apply MemLp.of_bound hv.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
  exact hC ⟨z, Metric.ball_subset_closedBall hz, rfl⟩

alias suAlpha_continuous_memLp_ball := continuous_memLp_ball

private theorem uniform_affine_chart_range
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℕ → LoopPlane → E) (u0 phi : LoopPlane → E) (hu0 : Continuous u0)
    (hphi : Continuous phi) (hlim : TendstoUniformly u u0 atTop)
    {S : Set LoopPlane} (hS : IsCompact S) (hSne : S.Nonempty) {c : E} {r : ℝ}
    (hval : ∀ z ∈ S, u0 z ∈ Metric.ball c r) :
    ∃ delta : ℝ, 0 < delta ∧
      (∀ t : ℝ, |t| < delta → ∀ z ∈ S, u0 z + t • phi z ∈ Metric.closedBall c r) ∧
      ∀ᶠ j in atTop, ∀ t : ℝ, |t| < delta →
        ∀ z ∈ S, u j z + t • phi z ∈ Metric.closedBall c r := by
  obtain ⟨z0, hz0, hmax⟩ := hS.exists_isMaxOn hSne
    (hu0.dist continuous_const).continuousOn
  let m := dist (u0 z0) c
  have hmr : m < r := hval z0 hz0
  obtain ⟨P0, hP0⟩ := hS.bddAbove_image hphi.norm.continuousOn
  let P := max P0 0
  have hP : 0 ≤ P := le_max_right _ _
  have hphiP (z) (hz : z ∈ S) : ‖phi z‖ ≤ P :=
    (hP0 ⟨z, hz, rfl⟩).trans (le_max_left _ _)
  let eta := (r - m) / 2
  let delta := eta / (P + 1)
  have heta : 0 < eta := by dsimp [eta]; linarith
  have hdelta : 0 < delta := div_pos heta (by linarith)
  have hpert (t : ℝ) (ht : |t| < delta) (z) (hz : z ∈ S) : ‖t • phi z‖ ≤ eta := by
    rw [norm_smul, Real.norm_eq_abs]
    have hsmall : |t| * (P + 1) < eta := (lt_div_iff₀ (by linarith)).mp ht
    have hb := mul_le_mul_of_nonneg_left (hphiP z hz) (abs_nonneg t)
    nlinarith
  refine ⟨delta, hdelta, ?_, ?_⟩
  · intro t ht z hz
    apply Metric.mem_closedBall.mpr
    have hdist : dist (u0 z + t • phi z) c ≤ dist (u0 z) c + ‖t • phi z‖ := by
      simpa only [dist_eq_norm, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
        norm_add_le (u0 z - c) (t • phi z)
    have hm : dist (u0 z) c ≤ m := hmax hz
    have hb := hpert t ht z hz
    dsimp [eta] at hb
    linarith
  · filter_upwards [Metric.tendstoUniformly_iff.mp hlim eta heta] with j hj t ht z hz
    apply Metric.mem_closedBall.mpr
    have hdist : dist (u j z + t • phi z) c ≤
        dist (u j z) (u0 z) + dist (u0 z) c + ‖t • phi z‖ := by
      have ha : dist (u j z + t • phi z) c ≤ dist (u j z) c + ‖t • phi z‖ := by
        simpa only [dist_eq_norm, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
          norm_add_le (u j z - c) (t • phi z)
      linarith [dist_triangle (u j z) (u0 z) c]
    have hjz : dist (u j z) (u0 z) < eta := by simpa only [dist_comm] using hj z
    have hm : dist (u0 z) c ≤ m := hmax hz
    have hb := hpert t ht z hz
    dsimp [eta] at hjz hb
    linarith

set_option maxHeartbeats 1600000 in

theorem suAlpha_attained_local_minimum [CompactSpace M] [T2Space M]
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
    ∃ (e : M → EuclideanSpace ℝ (Fin n)) (r r0 : ℝ)
      (V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)),
      ContMDiff (𝓡 n) (𝓡 n) ∞ e ∧ 0 < r ∧ 0 < r0 ∧
      Metric.closedBall (c (f0 p)) r0 ⊆ c.target ∧
      (∀ z ∈ Metric.closedBall (cs p) r,
        f0 (cs.symm z) ∈ c.source ∧ e (f0 (cs.symm z)) = c (f0 (cs.symm z))) ∧
      (∀ i, MemLp (V i) (ENNReal.ofReal (2 * alpha))
        (volume.restrict (Metric.ball (cs p) r))) ∧
      (∀ i (phi : LoopPlane → ℝ), ContDiff ℝ ∞ phi → HasCompactSupport phi →
        tsupport phi ⊆ Metric.ball (cs p) r →
        (∫ z in Metric.ball (cs p) r, phi z • V i z) =
          -(∫ z in Metric.ball (cs p) r,
            fderiv ℝ phi z (EuclideanSpace.basisFun (Fin 2) ℝ i) • c (f0 (cs.symm z)))) ∧
      ∀ phi : LoopPlane → EuclideanSpace ℝ (Fin n), ContDiff ℝ ∞ phi →
        HasCompactSupport phi → tsupport phi ⊆ Metric.ball (cs p) r →
        let state := fun z => (e (f0 (cs.symm z)), (V 0 z, V 1 z))
        let test := fun z => (phi z, suAlphaDerivativePair phi z)
        ∃ delta : ℝ, 0 < delta ∧ ∀ t : ℝ, |t| < delta →
          (∀ z ∈ Metric.closedBall (cs p) r,
            e (f0 (cs.symm z)) + t • phi z ∈ Metric.closedBall (c (f0 p)) r0) ∧
          IntegrableOn (fun z => suAlphaLocalDensity g (f0 p) alpha z (state z + t • test z))
            (Metric.ball (cs p) r) ∧
          (∫ z in Metric.ball (cs p) r, suAlphaLocalDensity g (f0 p) alpha z (state z)) ≤
            ∫ z in Metric.ball (cs p) r,
              suAlphaLocalDensity g (f0 p) alpha z (state z + t • test z) := by
  let : UniformSpace M := uniformSpaceOfCompactR1
  let c := chartAt (EuclideanSpace ℝ (Fin n)) (f0 p)
  let cs := chartAt LoopPlane p
  obtain ⟨e, r, r0, k, he, hr, hr0, hk, hKt, hlocal, htail, V, hVp, htest, hstrong⟩ :=
    suAlpha_minimizing_strong_derivatives g ha f hf hn hbound henergy f0 hlim p
  let O := Metric.ball (cs p) r
  let S := Metric.closedBall (cs p) r
  let K := Metric.closedBall (c (f0 p)) r0
  let mu := volume.restrict O
  let q := ENNReal.ofReal (2 * alpha)
  let : IsFiniteMeasure mu := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let u := fun j => e ∘ f (k j) ∘ cs.symm
  let u0 := e ∘ f0 ∘ cs.symm
  let state := fun z => (u0 z, (V 0 z, V 1 z))
  let W := fun j z => (u j z, suAlphaDerivativePair (u j) z)
  have hq : 1 ≤ q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hu (j : ℕ) : ContDiff ℝ ∞ (u j) :=
    contMDiff_iff_contDiff.mp (he.comp ((hf _).comp (suSphereChart_smooth p)))
  have hu0 : Continuous u0 := he.continuous.comp (f0.continuous.comp
    (suSphereChart_smooth p).continuous)
  have hpair (j : ℕ) : Continuous (suAlphaDerivativePair (u j)) :=
    (((hu j).continuous_fderiv (by simp)).clm_apply continuous_const).prodMk
      (((hu j).continuous_fderiv (by simp)).clm_apply continuous_const)
  have hW (j : ℕ) : MemLp (W j) q mu :=
    continuous_memLp_ball ((hu j).continuous.prodMk (hpair j)) (cs p) r q
  have hstate : MemLp state q mu := memLp_pair
    (continuous_memLp_ball hu0 (cs p) r q) (memLp_pair (hVp 0) (hVp 1))
  have hfU : TendstoUniformly f f0 atTop := tendstoUniformlyOn_univ.mp
    (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hlim univ isCompact_univ)
  have huU : TendstoUniformly u u0 atTop :=
    ((CompactSpace.uniformContinuous_of_continuous he.continuous).comp_tendstoUniformly
      (fun U hU => hk.tendsto_atTop.eventually (hfU U hU))).comp cs.symm
  have huLp : Tendsto (fun j => eLpNorm (u j - u0) q mu) atTop (𝓝 0) :=
    strong_of_uniform (fun j => (hu j).continuous.aestronglyMeasurable)
      hu0.aestronglyMeasurable huU
  have hdLp : Tendsto (fun j => eLpNorm (fun z =>
      suAlphaDerivativePair (u j) z - (V 0 z, V 1 z)) q mu) atTop (𝓝 0) :=
    strong_pair hq (fun j => ((hpair j).fst).aestronglyMeasurable)
      (fun j => ((hpair j).snd).aestronglyMeasurable) (hVp 0).1 (hVp 1).1
        ((hstrong 0).comp hk.tendsto_atTop) ((hstrong 1).comp hk.tendsto_atTop)
  have hWLp : Tendsto (fun j => eLpNorm (W j - state) q mu) atTop (𝓝 0) :=
    strong_pair hq (fun j => (hu j).continuous.aestronglyMeasurable)
      (fun j => (hpair j).aestronglyMeasurable) hu0.aestronglyMeasurable
        ((hVp 0).1.prodMk (hVp 1).1) huLp hdLp
  refine ⟨e, r, r0, fun i z => V i z, he, hr, hr0, hKt, fun z hz =>
    ⟨(hlocal z hz).1, (hlocal z hz).2.1⟩, hVp, htest, ?_⟩
  intro phi hphi hcompact hsub
  let test := fun z => (phi z, suAlphaDerivativePair phi z)
  have htestcont : Continuous test := hphi.continuous.prodMk
    (((hphi.continuous_fderiv (by simp)).clm_apply continuous_const).prodMk
      ((hphi.continuous_fderiv (by simp)).clm_apply continuous_const))
  have htestLp : MemLp test q mu := continuous_memLp_ball htestcont (cs p) r q
  obtain ⟨delta, hdelta, hrange0, hrange⟩ := uniform_affine_chart_range u u0 phi hu0
    hphi.continuous huU (isCompact_closedBall _ _) (Metric.nonempty_closedBall.mpr hr.le)
      (fun z hz => (hlocal z hz).2.2)
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((hk.tendsto_atTop.eventually htail).and hrange)
  have hKt' : K ⊆ (extChartAt (𝓡 n) (f0 p)).target := by
    intro y hy
    rw [extChartAt_target]
    exact ⟨hKt hy, ⟨y, rfl⟩⟩
  let Ws := fun j => W (j + N)
  have hshift := hWLp.comp (tendsto_add_atTop_nat N)
  have hvarlimit (t : ℝ) (ht : |t| < delta) :
      (∀ j, Integrable (fun z => suAlphaLocalDensity g (f0 p) alpha z
        (Ws j z + t • test z)) mu) ∧
      Integrable (fun z => suAlphaLocalDensity g (f0 p) alpha z
        (state z + t • test z)) mu ∧
      Tendsto (fun j => ∫ z, suAlphaLocalDensity g (f0 p) alpha z
        (Ws j z + t • test z) ∂mu) atTop
          (𝓝 (∫ z, suAlphaLocalDensity g (f0 p) alpha z (state z + t • test z) ∂mu)) ∧
      Tendsto (fun j => eLpNorm (fun z =>
        suAlphaLocalDensity g (f0 p) alpha z (Ws j z + t • test z) -
          suAlphaLocalDensity g (f0 p) alpha z (state z + t • test z)) 1 mu)
        atTop (𝓝 0) := by
    apply suAlpha_chart_integral_limit g ha p (f0 p) (isCompact_closedBall _ _) hKt'
      (fun j z => Ws j z + t • test z) (fun z => state z + t • test z)
    · exact fun j => (hW _).add (htestLp.const_smul t)
    · exact hstate.add (htestLp.const_smul t)
    · simpa only [Pi.sub_def, Ws, Function.comp_def, add_sub_add_right_eq_sub] using hshift
    · intro j
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
      exact (hN (j + N) (Nat.le_add_left _ _)).2 t ht z (Metric.ball_subset_closedBall hz)
    · filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
      exact hrange0 t ht z (Metric.ball_subset_closedBall hz)
  have hbase := hvarlimit 0 (by simpa using hdelta)
  simp only [zero_smul, add_zero] at hbase
  refine ⟨delta, hdelta, fun t ht => ⟨hrange0 t ht, (hvarlimit t ht).2.1, ?_⟩⟩
  have hcompare (j : ℕ) : sInf (m60NonNullAlphaEnergyValues g alpha) -
      m60SphereAlphaEnergy g alpha (f (k (j + N))) ≤
        (∫ z, suAlphaLocalDensity g (f0 p) alpha z (Ws j z + t • test z) ∂mu) -
          ∫ z, suAlphaLocalDensity g (f0 p) alpha z (Ws j z) ∂mu := by
    have hcoords : ∀ x ∈ cs.source ∩ cs ⁻¹' O,
        f (k (j + N)) x ∈ c.source ∧ e (f (k (j + N)) x) = c (f (k (j + N)) x) ∧
          e (f (k (j + N)) x) ∈ K := by
      intro x hx
      have hh := (hN (j + N) (Nat.le_add_left _ _)).1
        (cs x) (Metric.ball_subset_closedBall hx.2)
      rw [cs.left_inv hx.1] at hh
      exact ⟨hh.1, hh.2.1.self_of_nhds, Metric.ball_subset_closedBall hh.2.2⟩
    have hvar : ∀ z ∈ O, e (f (k (j + N)) (cs.symm z)) + t • phi z ∈ K :=
      fun z hz => (hN (j + N) (Nat.le_add_left _ _)).2 t ht z
        (Metric.ball_subset_closedBall hz)
    have hh := suAlpha_local_affine_comparison g (by linarith : 0 ≤ alpha) p (f0 p) t
      (f (k (j + N))) (hf _) (hn _) e he phi hphi hcompact hsub (convex_closedBall _ _)
        hKt hcoords hvar
    have hd (z : LoopPlane) : suAlphaDerivativePair (fun y => u (j + N) y + t • phi y) z =
        suAlphaDerivativePair (u (j + N)) z + t • suAlphaDerivativePair phi z := by
      have hh := ((hu (j + N)).differentiable (by simp) z).hasFDerivAt.add
        (((hphi.differentiable (by simp)) z).hasFDerivAt.const_smul t)
      have hh' : fderiv ℝ (fun y => u (j + N) y + t • phi y) z =
          fderiv ℝ (u (j + N)) z + t • fderiv ℝ phi z := hh.fderiv
      unfold suAlphaDerivativePair
      rw [hh']
      rfl
    change _ ≤ ∫ z in O,
      suAlphaLocalDensity g (f0 p) alpha z
        (u (j + N) z + t • phi z,
          suAlphaDerivativePair (fun y => u (j + N) y + t • phi y) z) -
        suAlphaLocalDensity g (f0 p) alpha z (W (j + N) z) at hh
    simp_rw [hd] at hh
    change _ ≤ ∫ z, suAlphaLocalDensity g (f0 p) alpha z (Ws j z + t • test z) -
      suAlphaLocalDensity g (f0 p) alpha z (Ws j z) ∂mu at hh
    rwa [integral_sub ((hvarlimit t ht).1 j) (hbase.1 j)] at hh
  have hE := henergy.comp (hk.tendsto_atTop.comp (tendsto_add_atTop_nat N))
  have hleft : Tendsto (fun j => sInf (m60NonNullAlphaEnergyValues g alpha) -
      m60SphereAlphaEnergy g alpha (f (k (j + N)))) atTop
        (𝓝 (sInf (m60NonNullAlphaEnergyValues g alpha) -
          sInf (m60NonNullAlphaEnergyValues g alpha))) := tendsto_const_nhds.sub hE
  have hright := (hvarlimit t ht).2.2.1.sub hbase.2.2.1
  have hineq := le_of_tendsto_of_tendsto' hleft hright hcompare
  change (∫ z, suAlphaLocalDensity g (f0 p) alpha z (state z) ∂mu) ≤
    ∫ z, suAlphaLocalDensity g (f0 p) alpha z (state z + t • test z) ∂mu
  exact sub_nonneg.mp (by simpa only [sub_self] using hineq)

set_option maxHeartbeats 1600000 in

theorem suAlpha_attained_weakChart [CompactSpace M] [T2Space M]
    (g : RiemannianMetric n M) {alpha C : ℝ} (ha : 1 ≤ alpha)
    (f : ℕ → UnitTwoSphere → M) (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) ∞ (f j))
    (hn : ∀ j, ¬ IsNullHomotopicSphere (f j))
    (hbound : ∀ j, m60SphereAlphaEnergy g alpha (f j) ≤ C)
    (henergy : Tendsto (fun j => m60SphereAlphaEnergy g alpha (f j)) atTop
      (𝓝 (sInf (m60NonNullAlphaEnergyValues g alpha))))
    (f0 : C(UnitTwoSphere, M))
    (hlim : Tendsto (fun j => (⟨f j, (hf j).continuous⟩ : C(UnitTwoSphere, M)))
      atTop (𝓝 f0)) (p : UnitTwoSphere) : Nonempty (SUWeakAlphaChart g alpha f0 p) := by
  obtain ⟨e, r, r0, V, he, hr, hr0, hKt, hlocal, hV, hweak, hminimum⟩ :=
    suAlpha_attained_local_minimum g ha f hf hn hbound henergy f0 hlim p
  let cs := chartAt LoopPlane p
  let c := chartAt (EuclideanSpace ℝ (Fin n)) (f0 p)
  let O := Metric.ball (cs p) r
  let S := Metric.closedBall (cs p) r
  let mu := volume.restrict O
  let u := e ∘ f0 ∘ cs.symm
  let q := ENNReal.ofReal (2 * alpha)
  let : IsFiniteMeasure mu := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hq : 1 ≤ q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hu : Continuous u := he.continuous.comp
    (f0.continuous.comp (suSphereChart_smooth p).continuous)
  have hueq : EqOn u (suAlphaChartCoordinate (n := n) f0 p) S :=
    fun z hz => (hlocal z hz).2
  have hueqae : u =ᵐ[mu] suAlphaChartCoordinate (n := n) f0 p := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact hueq (Metric.ball_subset_closedBall hz)
  have hup : MemLp (suAlphaChartCoordinate (n := n) f0 p) q mu :=
    MemLp.ae_eq hueqae (continuous_memLp_ball hu (cs p) r q)
  have hvariation (phi : LoopPlane → EuclideanSpace ℝ (Fin n))
      (hphi : ContDiff ℝ ∞ phi) (hcompact : HasCompactSupport phi)
      (hsub : tsupport phi ⊆ O) :
      IntegrableOn (suAlphaChartVariation g (f0 p) alpha
        (suAlphaChartCoordinate (n := n) f0 p) V phi) O ∧
      (∫ z in O, suAlphaChartVariation g (f0 p) alpha
        (suAlphaChartCoordinate (n := n) f0 p) V phi z) = 0 := by
    obtain ⟨delta, hdelta, hmin⟩ := hminimum phi hphi hcompact hsub
    have hzero : |(0 : ℝ)| < delta := by simpa using hdelta
    have hbase : IntegrableOn (fun z => suAlphaLocalDensity g (f0 p) alpha z
        (u z, (V 0 z, V 1 z))) O := by
      simpa only [zero_smul, add_zero, u, O, cs, Function.comp_apply] using! (hmin 0 hzero).2.1
    have hK : Metric.closedBall (c (f0 p)) r0 ⊆ (extChartAt (𝓡 n) (f0 p)).target := by
      simpa using hKt
    have hder := suAlpha_integral_firstVariation g (f0 p) ha u phi hu hphi V (cs p) r
      hV (isCompact_closedBall _ _) hK hdelta (fun t ht => (hmin t ht).1) hbase
    let energy := fun t : ℝ => ∫ z in O, suAlphaLocalDensity g (f0 p) alpha z
      ((u z, (V 0 z, V 1 z)) + t • (phi z, suAlphaDerivativePair phi z))
    have hmin0 : IsLocalMin energy 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hdelta] with t ht
      have ht' : |t| < delta := by
        simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
      simpa only [energy, zero_smul, add_zero, u, O, cs, Function.comp_apply] using!
        (hmin t ht').2.2
    have hstat : (∫ z in O, suAlphaChartVariation g (f0 p) alpha u V phi z) = 0 :=
      hmin0.hasDerivAt_eq_zero hder.2
    have heq : suAlphaChartVariation g (f0 p) alpha u V phi =ᵐ[mu]
        suAlphaChartVariation g (f0 p) alpha (suAlphaChartCoordinate (n := n) f0 p) V phi := by
      filter_upwards [hueqae] with z hz
      simp only [suAlphaChartVariation, hz]
    exact ⟨hder.1.congr heq, (integral_congr_ae heq).symm.trans hstat⟩
  refine ⟨{
    radius := r
    radius_pos := hr
    chart_range := fun z hz => (hlocal z hz).1
    coordinate_continuous := hu.continuousOn.congr (fun z hz => (hueq hz).symm)
    coordinate_memLp := hup
    column := V
    column_memLp := hV
    weak_derivative := ?_
    variation_integrable := fun phi hphi hc hs => (hvariation phi hphi hc hs).1
    variation_zero := fun phi hphi hc hs => (hvariation phi hphi hc hs).2
  }⟩
  intro i a phi hphi hcompact hsub
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin n => ℝ) a
  have hleft : Integrable (fun z => phi z • V i z) mu :=
    (MemLp.integrable hq (hV i)).locallyIntegrable.integrable_smul_left_of_hasCompactSupport
      hphi.continuous hcompact
  have hright : Integrable (fun z =>
      fderiv ℝ phi z (EuclideanSpace.basisFun (Fin 2) ℝ i) •
        suAlphaChartCoordinate (n := n) f0 p z) mu :=
    (MemLp.integrable hq hup).locallyIntegrable.integrable_smul_left_of_hasCompactSupport
      ((hphi.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hcompact.fderiv_apply ℝ _)
  have hh := congrArg L (hweak i phi hphi hcompact hsub)
  change L (∫ z, phi z • V i z ∂mu) = L (-(∫ z,
    fderiv ℝ phi z (EuclideanSpace.basisFun (Fin 2) ℝ i) •
      suAlphaChartCoordinate (n := n) f0 p z ∂mu)) at hh
  rw [map_neg, ← L.integral_comp_comm hleft, ← L.integral_comp_comm hright] at hh
  have hh' := congrArg Neg.neg hh
  simp only [neg_neg] at hh'
  simpa only [L, PiLp.proj_apply, map_smul, smul_eq_mul, EuclideanSpace.basisFun_apply,
    suAlphaChartCoordinate, Function.comp_apply, mul_comm] using hh'.symm

end M60

theorem m60_exists_nonNull_weakAlphaSphere
    [CompactSpace M] [T2Space M] [SecondCountableTopology M]
    (g : RiemannianMetric n M) (x : M) (hpi : Nontrivial (HomotopyGroup.Pi 2 M x))
    {eps0 alpha : ℝ} (ha : alpha ∈ Ioo 1 (1 + eps0)) (h2 : alpha ≤ 2) :
    ∃ u : M60.SUWeakAlphaSphere g eps0 alpha, ¬ IsNullHomotopicSphere u.map ∧
      ∃ (C : ℝ) (f : ℕ → UnitTwoSphere → M)
        (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) ∞ (f j)),
        (∀ j, ¬ IsNullHomotopicSphere (f j)) ∧
        (∀ j, m60SphereAlphaEnergy g alpha (f j) ≤ C) ∧
        Tendsto (fun j => m60SphereAlphaEnergy g alpha (f j)) atTop
          (𝓝 (sInf (m60NonNullAlphaEnergyValues g alpha))) ∧
        Tendsto (fun j => (⟨f j, (hf j).continuous⟩ : C(UnitTwoSphere, M))) atTop (𝓝 u.map) := by
  obtain ⟨C, _, hseq⟩ := m60SphereAlphaEnergy_bounded_minimizing_sequences g x hpi
  obtain ⟨f, hf, hn, hbound, henergy⟩ := hseq alpha ha.1.le h2
  obtain ⟨f0, k, hk, hn0, hlim⟩ := m60SphereAlphaEnergy_nonNull_subsequence g ha.1
    f hf hn (fun j => (hbound j).le)
  let F := fun j => f (k j)
  have hF (j) : ContMDiff (𝓡 2) (𝓡 n) ∞ (F j) := hf _
  have hFn (j) : ¬ IsNullHomotopicSphere (F j) := hn _
  have hFb (j) : m60SphereAlphaEnergy g alpha (F j) ≤ C := (hbound _).le
  have hFe := henergy.comp hk.tendsto_atTop
  have hchart (p) : Nonempty (M60.SUWeakAlphaChart g alpha f0 p) :=
    M60.suAlpha_attained_weakChart g ha.1.le F hF hFn hFb hFe f0 hlim p
  let u : M60.SUWeakAlphaSphere g eps0 alpha :=
    ⟨ha, f0, fun p => Classical.choice (hchart p)⟩
  exact ⟨u, hn0, C, F, hF, hFn, hFb, hFe, hlim⟩

end PoincareConjecture
