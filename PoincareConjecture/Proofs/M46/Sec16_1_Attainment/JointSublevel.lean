import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.ExponentialSublevel
import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.VaryingTimeSurvival










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}




theorem exponential_joint_action_sublevel_compact
    (hM04 : RicciFlowCurvatureTheory.{0})
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (LG : GeneralizedLGeometryConclusion G)
    (E : M14ExponentialFamily G T x) {a c D : ℝ} (ha : 0 < a) (hD : 0 ≤ D)
    (htime : ∀ b ∈ Icc a c, T - b ^ 2 ∈ I.domain)
    {K : Set G.Point} (hK : IsCompact K)
    (hconf : ∀ Z b, b ∈ Icc a c → (Z, b) ∈ E.domain → E.action Z b ≤ D →
      MapsTo (E.gamma Z) (Icc 0 b) K) :
    IsCompact {z : G.Horizontal x × ℝ |
      z.2 ∈ Icc a c ∧ z ∈ E.domain ∧ E.action z.1 z.2 ≤ D} := by
  classical
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  let : FiniteDimensional ℝ (G.Horizontal x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n)) G.Horizontal x
  let : FirstCountableTopology (G.Horizontal x × ℝ) := UniformSpace.firstCountableTopology _
  let : SequentialSpace (G.Horizontal x × ℝ) :=
    @FrechetUrysohnSpace.to_sequentialSpace _ _
      FirstCountableTopology.frechetUrysohnSpace
  obtain ⟨CR, Cgrad, hCR, hCgrad, hRic, hgrad⟩ := compact_cage_analytic_bounds hM12 hK
  obtain ⟨C, hC, henergy⟩ := exponential_square_energy_uniform_bound hM12 E
    (H := c) ha hD hCR hCgrad hRic hgrad
  let B : Set (G.Horizontal x × ℝ) :=
    {z | z.2 ∈ Icc a c ∧ z ∈ E.domain ∧ E.action z.1 z.2 ≤ D}
  have henergyB (z : G.Horizontal x × ℝ) (hz : z ∈ B)
      (s : ℝ) (hs : s ∈ Icc 0 z.2) :
      G.spacetime.horizontalMetric.inner
        ((E.square_path z.1 z.2 hz.2.1 (ha.trans_le hz.1.1)).curve s)
        ((E.square_path z.1 z.2 hz.2.1 (ha.trans_le hz.1.1)).horizontal_velocity s)
        ((E.square_path z.1 z.2 hz.2.1 (ha.trans_le hz.1.1)).horizontal_velocity s) ≤ C :=
    henergy z.1 z.2 hz.1.1 hz.1.2 hz.2.1 hz.2.2
      (fun r hr => hconf z.1 z.2 hz.1 hz.2.1 hz.2.2 hr) s hs
  have hclosed : IsClosed B := by
    apply IsSeqClosed.isClosed
    intro zs z hzs hlim
    have ht : z.2 ∈ Icc a c := isClosed_Icc.mem_of_tendsto
      (continuous_snd.continuousAt.tendsto.comp hlim)
      (Eventually.of_forall fun k => (hzs k).1)
    have hz : z ∈ E.domain := exponential_survival_of_varying_phase_limit hM04 hM12 E
      (ha.trans_le ht.1) (htime z.2 ht)
      (continuous_fst.continuousAt.tendsto.comp hlim)
      (continuous_snd.continuousAt.tendsto.comp hlim)
      (fun k => ha.trans_le (hzs k).1.1) (fun k => (hzs k).2.1) hK C
      (fun k s hs => hconf (zs k).1 (zs k).2 (hzs k).1 (hzs k).2.1 (hzs k).2.2 hs)
      (fun k s hs => henergyB (zs k) (hzs k) s hs)
    have hwithin : Tendsto zs atTop (𝓝[E.domain ∩ {w | 0 < w.2}] z) :=
      tendsto_nhdsWithin_iff.mpr ⟨hlim,
        Eventually.of_forall fun k => ⟨(hzs k).2.1, ha.trans_le (hzs k).1.1⟩⟩
    have haction := (LG.exponential.action_differential T x E).1.continuousOn
      z ⟨hz, ha.trans_le ht.1⟩
    exact ⟨ht, hz, le_of_tendsto (Filter.Tendsto.comp haction hwithin)
      (Eventually.of_forall fun k => (hzs k).2.2)⟩
  have hbounded : B ⊆ Metric.closedBall (0 : G.Horizontal x) (Real.sqrt C) ×ˢ Icc a c := by
    intro z hz
    have hb : 0 < z.2 := ha.trans_le hz.1.1
    let Q : M14SquareRootInitialValuePath G T (z.2 ^ 2) x (E.gamma z.1 z.2) z.1 := {
      path := E.path z.1 z.2 hz.2.1 hb
      square_path := E.square_path z.1 z.2 hz.2.1 hb
      extension := E.square_extension z.1 z.2 hz.2.1 hb
      euler := E.square_euler z.1 z.2 hz.2.1 hb
      initial_velocity := E.square_initial_velocity z.1 z.2 hz.2.1 hb }
    have hbound := henergyB z hz 0 ⟨le_rfl, hb.le⟩
    change G.spacetime.horizontalMetric.inner (Q.square_path.curve 0)
      (Q.square_path.horizontal_velocity 0) (Q.square_path.horizontal_velocity 0) ≤ C at hbound
    rw [initialValue_energy_zero Q] at hbound
    change 4 * inner ℝ z.1 z.1 ≤ C at hbound
    rw [real_inner_self_eq_norm_sq] at hbound
    have hnorm : ‖z.1‖ ≤ Real.sqrt C := by
      nlinarith [Real.sq_sqrt hC, Real.sqrt_nonneg C, norm_nonneg z.1, sq_nonneg ‖z.1‖]
    exact ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm, hz.1⟩
  have hcompact := (isCompact_closedBall (0 : G.Horizontal x) (Real.sqrt C)).prod
    (isCompact_Icc : IsCompact (Icc a c))
  exact hcompact.of_isClosed_subset hclosed hbounded

end PoincareConjecture.Proofs.M46
