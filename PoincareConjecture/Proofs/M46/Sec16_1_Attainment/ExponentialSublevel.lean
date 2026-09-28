import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Cor6_67_CompactMinimizers











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}




theorem exponential_action_sublevel_compact
    (hM04 : RicciFlowCurvatureTheory.{0})
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (LG : GeneralizedLGeometryConclusion G)
    (E : M14ExponentialFamily G T x) {b : ℝ} (hb : 0 < b)
    {D : ℝ} (hD : 0 ≤ D) {K : Set G.Point} (hK : IsCompact K)
    (hconf : ∀ Z : G.Horizontal x, (Z, b) ∈ E.domain → E.action Z b ≤ D →
      MapsTo (E.gamma Z) (Icc 0 b) K) :
    IsCompact {Z : G.Horizontal x | (Z, b) ∈ E.domain ∧ E.action Z b ≤ D} := by
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
  let : FirstCountableTopology (G.Horizontal x) := UniformSpace.firstCountableTopology _
  let : SequentialSpace (G.Horizontal x) :=
    @FrechetUrysohnSpace.to_sequentialSpace _ _
      FirstCountableTopology.frechetUrysohnSpace
  obtain ⟨CR, Cgrad, hCR, hCgrad, hRic, hgrad⟩ := compact_cage_analytic_bounds hM12 hK
  obtain ⟨C, hC, henergy⟩ := exponential_square_energy_uniform_bound hM12 E
    (H := b) hb hD hCR hCgrad hRic hgrad
  let B : Set (G.Horizontal x) := {Z | (Z, b) ∈ E.domain ∧ E.action Z b ≤ D}
  have henergyB (Z : G.Horizontal x) (hZB : Z ∈ B)
      (s : ℝ) (hs : s ∈ Icc 0 b) :
      G.spacetime.horizontalMetric.inner ((E.square_path Z b hZB.1 hb).curve s)
        ((E.square_path Z b hZB.1 hb).horizontal_velocity s)
        ((E.square_path Z b hZB.1 hb).horizontal_velocity s) ≤ C :=
    henergy Z b le_rfl le_rfl hZB.1 hZB.2
      (fun r hr => hconf Z hZB.1 hZB.2 hr) s hs
  have hclosed : IsClosed B := by
    apply IsSeqClosed.isClosed
    intro Zs Z hZs hlim
    have hZ : (Z, b) ∈ E.domain := exponential_survival_of_uniform_phase_limit hM04 hM12 E
      hb hlim (fun k => (hZs k).1) hK C
      (fun k s hs => hconf (Zs k) (hZs k).1 (hZs k).2 hs)
      (fun k s hs => henergyB (Zs k) (hZs k) s hs)
    have hactionLim : Tendsto (fun k => E.action (Zs k) b) atTop (𝓝 (E.action Z b)) :=
      ((LG.exponential.action_differential T x E).2 Z b hZ hb).1.continuousAt.tendsto.comp hlim
    exact ⟨hZ, le_of_tendsto hactionLim (Eventually.of_forall fun k => (hZs k).2)⟩
  have hbounded : B ⊆ Metric.closedBall (0 : G.Horizontal x) (Real.sqrt C) := by
    intro Z hZB
    let Q : M14SquareRootInitialValuePath G T (b ^ 2) x (E.gamma Z b) Z := {
      path := E.path Z b hZB.1 hb
      square_path := E.square_path Z b hZB.1 hb
      extension := E.square_extension Z b hZB.1 hb
      euler := E.square_euler Z b hZB.1 hb
      initial_velocity := E.square_initial_velocity Z b hZB.1 hb }
    have hbound := henergyB Z hZB 0 ⟨le_rfl, hb.le⟩
    change G.spacetime.horizontalMetric.inner (Q.square_path.curve 0)
      (Q.square_path.horizontal_velocity 0) (Q.square_path.horizontal_velocity 0) ≤ C at hbound
    rw [initialValue_energy_zero Q] at hbound
    change 4 * inner ℝ Z Z ≤ C at hbound
    rw [real_inner_self_eq_norm_sq] at hbound
    have hnorm : ‖Z‖ ≤ Real.sqrt C := by
      nlinarith [Real.sq_sqrt hC, Real.sqrt_nonneg C, norm_nonneg Z, sq_nonneg ‖Z‖]
    simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm
  exact (isCompact_closedBall (0 : G.Horizontal x) (Real.sqrt C)).of_isClosed_subset
    hclosed hbounded

end PoincareConjecture.Proofs.M46
