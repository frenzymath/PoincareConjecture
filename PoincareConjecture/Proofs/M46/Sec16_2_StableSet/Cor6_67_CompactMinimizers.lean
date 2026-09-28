import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_4_CompactPhaseContinuation
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Cor6_67_CompactAnalyticBounds
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Cor6_67_ExponentialEnergy
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Cor6_67_MinimizerClosure
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Cor6_67_FiniteBranches
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

private theorem minimizing_parameter_congr
    (E : M14ExponentialFamily G T x) (Z : G.Horizontal x)
    {a b : ℝ} (hab : a = b) (ha : 0 < a) (hb : 0 < b)
    (hZa : (Z, a) ∈ E.domain) (hZb : (Z, b) ∈ E.domain) :
    M14IsMinimizing (E.path Z a hZa ha) ↔ M14IsMinimizing (E.path Z b hZb hb) := by
  subst b
  rfl

theorem represented_minimizer_action
    (E : M14ExponentialFamily G T x) {b : ℝ} (hb : 0 < b)
    {y : G.Point} (p : M14BackwardPath G T 0 (b ^ 2) x y)
    {Z : G.Horizontal x} (hZ : (Z, b) ∈ E.domain)
    (htrace : EqOn p.curve (fun s => E.gamma Z (Real.sqrt s)) (Icc 0 (b ^ 2))) :
    E.action Z b = M14BackwardLAction G p ∧
      (M14IsMinimizing p ↔ M14IsMinimizing (E.path Z b hZ hb)) := by
  have hy : y = E.gamma Z b := by
    have h := p.curve_end.symm.trans (htrace ⟨sq_nonneg b, le_rfl⟩)
    simpa only [Real.sqrt_sq hb.le] using h
  subst y
  have heq : EqOn (E.path Z b hZ hb).curve p.curve (Ioo 0 (b ^ 2)) := by
    intro s hs
    exact (E.path_coherent Z b hZ hb s (Ioo_subset_Icc_self hs)).trans
      (htrace (Ioo_subset_Icc_self hs)).symm
  exact ⟨(E.action_eq Z b hZ hb).trans (M14.action_eq_of_curve_eqOn _ _ heq),
    (M14.isMinimizing_iff_of_curve_eqOn _ _ heq).symm⟩

theorem exists_compact_minimizing_capture
    (hM04 : RicciFlowCurvatureTheory.{0})
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (LG : GeneralizedLGeometryConclusion G)
    (E : M14ExponentialFamily G T x) {b : ℝ} (hb : 0 < b)
    (q0 : (G.slices (T - b ^ 2)).Point)
    (htime : T - b ^ 2 ∈ interior I.domain)
    {A : Set (G.slices (T - b ^ 2)).Point} (hA : IsClosed A)
    (hmin : ∀ q ∈ A, ∃ p : M14BackwardPath G T 0 (b ^ 2) x q.val,
      M14IsMinimizing p)
    {D : ℝ} (hD : 0 ≤ D)
    (haction : ∀ q ∈ A, ∀ p : M14BackwardPath G T 0 (b ^ 2) x q.val,
      M14IsMinimizing p → M14BackwardLAction G p ≤ D)
    {K : Set G.Point} (hK : IsCompact K)
    (hconf : ∀ Z : G.Horizontal x, (Z, b) ∈ E.domain → E.action Z b ≤ D →
      MapsTo (E.gamma Z) (Icc 0 b) K) :
    ∃ B : Set (G.Horizontal x), IsCompact B ∧
      (∀ Z ∈ B, ∃ hZ : (Z, b) ∈ E.domain, M14IsMinimizing (E.path Z b hZ hb)) ∧
      ∀ q ∈ A, ∀ p : M14BackwardPath G T 0 (b ^ 2) x q.val,
        M14IsMinimizing p → ∃ Z ∈ B,
          EqOn p.curve (fun s => E.gamma Z (Real.sqrt s)) (Icc 0 (b ^ 2)) ∧
          survivalSliceMap E (b ^ 2) (sq_nonneg b) q0 Z = q := by
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
  let f := survivalSliceMap E (b ^ 2) (sq_nonneg b) q0
  let B : Set (G.Horizontal x) := {Z | ∃ hZ : (Z, b) ∈ E.domain,
    M14IsMinimizing (E.path Z b hZ hb) ∧ f Z ∈ A ∧ E.action Z b ≤ D}
  obtain ⟨C, hC, henergy⟩ := exponential_square_energy_uniform_bound hM12 E
    (H := b) hb hD hCR hCgrad hRic hgrad
  have henergyB (Z : G.Horizontal x) (hZB : Z ∈ B)
      (hZ : (Z, b) ∈ E.domain) (s : ℝ) (hs : s ∈ Icc 0 b) :
      G.spacetime.horizontalMetric.inner ((E.square_path Z b hZ hb).curve s)
        ((E.square_path Z b hZ hb).horizontal_velocity s)
        ((E.square_path Z b hZ hb).horizontal_velocity s) ≤ C := by
    obtain ⟨_, _, _, hZD⟩ := hZB
    exact henergy Z b le_rfl le_rfl hZ hZD (fun r hr => hconf Z hZ hZD hr) s hs
  have hclosed : IsClosed B := by
    apply IsSeqClosed.isClosed
    intro Zs Z hZs hlim
    have hall : ∀ k, ∃ hZ : (Zs k, b) ∈ E.domain,
        M14IsMinimizing (E.path (Zs k) b hZ hb) ∧ f (Zs k) ∈ A ∧ E.action (Zs k) b ≤ D := hZs
    choose hsurv hmins hends hactions using hall
    have hZ : (Z, b) ∈ E.domain := exponential_survival_of_uniform_phase_limit hM04 hM12 E
      hb hlim hsurv hK C
      (fun k s hs => hconf (Zs k) (hsurv k) (hactions k) hs)
      (fun k s hs => henergyB (Zs k) (hZs k) (hsurv k) s hs)
    have hZsqrt : (Z, Real.sqrt (b ^ 2)) ∈ E.domain := by
      simpa only [Real.sqrt_sq hb.le] using hZ
    have hsurvSqrt : ∀ k, (Zs k, Real.sqrt (b ^ 2)) ∈ E.domain := by
      simpa only [Real.sqrt_sq hb.le] using hsurv
    have hminsSqrt : ∀ k, M14IsMinimizing
        (E.path (Zs k) (Real.sqrt (b ^ 2)) (hsurvSqrt k)
          (Real.sqrt_pos.mpr (sq_pos_of_pos hb))) := by
      intro k
      exact (minimizing_parameter_congr E (Zs k) (Real.sqrt_sq hb.le)
        _ hb (hsurvSqrt k) (hsurv k)).mpr (hmins k)
    have hendsLim : Tendsto (fun k => f (Zs k)) atTop (𝓝 (f Z)) :=
      (survivalSliceMap_smooth E (sq_nonneg b) q0 hZsqrt).continuousAt.tendsto.comp hlim
    have hZA : f Z ∈ A := hA.mem_of_tendsto hendsLim (Eventually.of_forall hends)
    have hZmin : M14IsMinimizing (E.path Z b hZ hb) := by
      exact (minimizing_parameter_congr E Z (Real.sqrt_sq hb.le) _ hb hZsqrt hZ).mp
        (minimizing_exponential_limit hM12 LG E (sq_pos_of_pos hb) q0 hlim
          hsurvSqrt hminsSqrt hZsqrt htime (hmin (f Z) hZA))
    have hactionLim : Tendsto (fun k => E.action (Zs k) b) atTop (𝓝 (E.action Z b)) :=
      ((LG.exponential.action_differential T x E).2 Z b hZ hb).1.continuousAt.tendsto.comp hlim
    exact ⟨hZ, hZmin, hZA, le_of_tendsto hactionLim (Eventually.of_forall hactions)⟩
  have hbounded : B ⊆ Metric.closedBall (0 : G.Horizontal x) (Real.sqrt C) := by
    intro Z hZB
    obtain ⟨hZ, _, _, _⟩ := (show Z ∈ B from hZB)
    let Q : M14SquareRootInitialValuePath G T (b ^ 2) x (E.gamma Z b) Z := {
      path := E.path Z b hZ hb
      square_path := E.square_path Z b hZ hb
      extension := E.square_extension Z b hZ hb
      euler := E.square_euler Z b hZ hb
      initial_velocity := E.square_initial_velocity Z b hZ hb }
    have hbound := henergyB Z hZB hZ 0 ⟨le_rfl, hb.le⟩
    change G.spacetime.horizontalMetric.inner (Q.square_path.curve 0)
      (Q.square_path.horizontal_velocity 0) (Q.square_path.horizontal_velocity 0) ≤ C at hbound
    rw [initialValue_energy_zero Q] at hbound
    change 4 * inner ℝ Z Z ≤ C at hbound
    rw [real_inner_self_eq_norm_sq] at hbound
    have hnorm : ‖Z‖ ≤ Real.sqrt C := by
      nlinarith [Real.sq_sqrt hC, Real.sqrt_nonneg C, norm_nonneg Z, sq_nonneg ‖Z‖]
    simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm
  refine ⟨B, (isCompact_closedBall (0 : G.Horizontal x) (Real.sqrt C)).of_isClosed_subset
    hclosed hbounded, ?_, ?_⟩
  · intro Z hZB
    obtain ⟨hZ, hminZ, _, _⟩ := hZB
    exact ⟨hZ, hminZ⟩
  · intro q hq p hp
    obtain ⟨Z, hZsqrt, htrace, hend⟩ := minimizing_exponential_branch LG E p hp
    have hZ : (Z, b) ∈ E.domain := by simpa only [Real.sqrt_sq hb.le] using hZsqrt
    obtain ⟨hact, hminimal⟩ := represented_minimizer_action E hb p hZ htrace
    have hpoint : f Z = q := by
      apply Subtype.ext
      exact (survivalSliceMap_val E (sq_nonneg b) q0 hZsqrt).trans hend
    refine ⟨Z, ⟨hZ, hminimal.mp hp, ?_, hact.le.trans (haction q hq p hp)⟩, htrace, hpoint⟩
    rw [hpoint]
    exact hq

theorem stable_image_full_measure_of_confined_actions
    (hM04 : RicciFlowCurvatureTheory.{0})
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (LG : GeneralizedLGeometryConclusion G)
    (E : M14ExponentialFamily G T x) {b : ℝ} (hb : 0 < b)
    (H : M14StableSet G T (b ^ 2) x E)
    (q0 : (G.slices (T - b ^ 2)).Point)
    (htime : T - b ^ 2 ∈ interior I.domain)
    {A : Set (G.slices (T - b ^ 2)).Point} (hA : IsOpen A)
    (hmin : ∀ q ∈ closure A, ∃ p : M14BackwardPath G T 0 (b ^ 2) x q.val,
      M14IsMinimizing p)
    {D : ℝ} (hD : 0 ≤ D)
    (haction : ∀ q ∈ closure A, ∀ p : M14BackwardPath G T 0 (b ^ 2) x q.val,
      M14IsMinimizing p → M14BackwardLAction G p ≤ D)
    {K : Set G.Point} (hK : IsCompact K)
    (hconf : ∀ Z : G.Horizontal x, (Z, b) ∈ E.domain → E.action Z b ≤ D →
      MapsTo (E.gamma Z) (Icc 0 b) K) :
    calibratedMetricVolume (G.slices (T - b ^ 2)).metricOnPoints
      (A \ H.endpoint_slice_map '' H.carrier) = 0 := by
  classical
  obtain ⟨B, hB, hsurv, hcapture⟩ := exists_compact_minimizing_capture hM04 hM12 LG E hb
    q0 htime isClosed_closure hmin hD haction hK hconf
  choose hBD hBmin using hsurv
  have hBDsqrt : ∀ Z ∈ B, (Z, Real.sqrt (b ^ 2)) ∈ E.domain := by
    simpa only [Real.sqrt_sq hb.le] using hBD
  have hBminsqrt : ∀ Z (hZB : Z ∈ B), M14IsMinimizing
      (E.path Z (Real.sqrt (b ^ 2)) (hBDsqrt Z hZB) (Real.sqrt_pos.mpr H.tau_pos)) := by
    intro Z hZB
    exact (minimizing_parameter_congr E Z (Real.sqrt_sq hb.le)
      _ hb (hBDsqrt Z hZB) (hBD Z hZB)).mpr (hBmin Z hZB)
  exact stable_image_full_measure_of_compact_minimizers hM04 hM12 LG E H q0 hA hB hBDsqrt
    hBminsqrt (fun q hq => hmin q (subset_closure hq))
    (fun q hq p hp => hcapture q (subset_closure hq) p hp)

end PoincareConjecture.Proofs.M46
