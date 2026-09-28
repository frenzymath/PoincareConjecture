import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Cor6_67_CompactMinimizers
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_StableImage
import PoincareConjecture.Proofs.M15.Thm8_10_StableSurvival
import PoincareConjecture.Proofs.M04

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M47

open Proofs.M46

theorem seedM15_generalized_configuration
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (hM14 : GeneralizedLGeometryTheory.{u} 3)
    {X : Type u} [TopologicalSpace X] {time : X → ℝ} {I : SpacetimeInterval}
    (G : GeneralizedLGeometryTransport 3 X time I)
    {T start tau L taubar l0 V r : ℝ} (x : (G.slices T).Point)
    {K : SpacetimeInterval} {C : Type u} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) C] [IsManifold (𝓡 3) ∞ C]
    [T2Space C] [SecondCountableTopology C]
    (B : M15ActualBallCylinder G T x r K C)
    (hcompact : IsCompact (closure ((G.slices T).metricOnPoints.ball x r)))
    (confinement : ActionConfinement G T start x.val)
    (region : MinimizingRegion G T start x.val confinement)
    (htau : 0 < tau) (htauStart : tau ≤ T - start) (htauTop : tau ≤ taubar)
    (hradius : r ^ 2 ≤ tau) (htime : T - tau ∈ interior I.domain)
    (hL : 0 ≤ L) (hbarrier : L < confinement.barrier)
    (hnormalized : L ≤ 2 * l0 * Real.sqrt tau)
    (A : Set (G.slices (T - tau)).Point) (hA : IsOpen A) (hne : A.Nonempty)
    (hvolume : ENNReal.ofReal V ≤
      calibratedMetricVolume (G.slices (T - tau)).metricOnPoints A)
    (hpaths : ∀ q ∈ closure A, ∃ path : M14BackwardPath G T 0 tau x.val q.val,
      M14BackwardLAction G path ≤ L) :
    ∃ E : M14ExponentialFamily G T x.val,
      Nonempty (M15Theorem81Configuration G T x E taubar l0 V r K C B) := by
  generalize hb : Real.sqrt tau = b at *
  have hbpos : 0 < b := hb ▸ Real.sqrt_pos.mpr htau
  have hbsq : b ^ 2 = tau := by rw [← hb, Real.sq_sqrt htau.le]
  subst tau
  have hmin (q : (G.slices (T - b ^ 2)).Point) (hq : q ∈ closure A) :
      ∃ path : M14BackwardPath G T 0 (b ^ 2) x.val q.val, M14IsMinimizing path := by
    obtain ⟨competitor, hcompetitor⟩ := hpaths q hq
    have hclock : G.spacetime.timeFunction q.val = T - b ^ 2 := q.property
    have hback : T - G.spacetime.timeFunction q.val = b ^ 2 := by rw [hclock]; ring
    have hregion : q.val ∈ region.region := by
      apply (region.region_exact q.val).mpr
      refine ⟨?_, ?_⟩
      · rw [hclock]
        exact ⟨by linarith, by linarith⟩
      · rw [hback]
        exact ⟨competitor, hcompetitor.trans_lt hbarrier⟩
    have h := region.minimizing q.val hregion
    rwa [hback] at h
  have haction (q : (G.slices (T - b ^ 2)).Point) (hq : q ∈ closure A)
      (path : M14BackwardPath G T 0 (b ^ 2) x.val q.val) (hpath : M14IsMinimizing path) :
      M14BackwardLAction G path ≤ L := by
    obtain ⟨competitor, hcompetitor⟩ := hpaths q hq
    exact (hpath competitor).trans hcompetitor
  obtain ⟨LG⟩ := hM14.conclusion X time I G
  obtain ⟨E⟩ := LG.exponential.family T x.val x.property
  obtain ⟨q0, hq0⟩ := hne
  obtain ⟨m0, hm0⟩ := hmin q0 (subset_closure hq0)
  obtain ⟨stable⟩ := Proofs.M15.exists_stableSet_of_minimizing LG E m0 hm0
  have hconf (Z : G.Horizontal x.val) (hZ : (Z, b) ∈ E.domain)
      (hZaction : E.action Z b ≤ L) : MapsTo (E.gamma Z) (Icc 0 b) confinement.cage := by
    let path := E.path Z b hZ hbpos
    have hpathAction : M14BackwardLAction G path < confinement.barrier := by
      rw [← E.action_eq Z b hZ hbpos]
      exact hZaction.trans_lt hbarrier
    have htrace := confinement.paths_mem (b ^ 2) htau htauStart
      (E.gamma Z b) path hpathAction
    intro s hs
    have hsq : s ^ 2 ∈ Icc 0 (b ^ 2) :=
      ⟨sq_nonneg s, (sq_le_sq₀ hs.1 hbpos.le).mpr hs.2⟩
    have heq := E.path_coherent Z b hZ hbpos (s ^ 2) hsq
    rw [Real.sqrt_sq hs.1] at heq
    rw [← heq]
    exact htrace hsq
  have hnull := stable_image_full_measure_of_confined_actions ricciFlowCurvatureTheory.{0}
    hM12 LG E hbpos stable q0 htime hA hmin hL haction confinement.cage_compact hconf
  have hlength (q : (G.slices (T - b ^ 2)).Point) (hq : q ∈ A) :
      M14ReducedLengthValue G T 0 (b ^ 2) x.val q.val ≤ l0 := by
    obtain ⟨path, hpath⟩ := hmin q (subset_closure hq)
    change M14ActionValue G T 0 (b ^ 2) x.val q.val / (2 * Real.sqrt (b ^ 2)) ≤ l0
    rw [Real.sqrt_sq hbpos.le, ← M14.action_eq_actionValue_of_minimizing path hpath]
    apply (div_le_iff₀ (by positivity : 0 < 2 * b)).mpr
    exact (haction q (subset_closure hq) path hpath).trans (by nlinarith [hnormalized])
  obtain ⟨W, hWopen, hWS, hWlength, hWvolume⟩ :=
    stable_source_of_open_comparison stable A hA hlength hvolume hnull
  exact ⟨E, ⟨{
    tau₀ := b ^ 2
    tau₀_pos := htau
    tau₀_le := htauTop
    radius_sq_le_tau₀ := hradius
    terminal_mem := interior_subset htime
    terminal_ball_compact := hcompact
    stable := stable
    W := W
    W_open := hWopen
    W_subset_stable := hWS
    normalized_reduced_length := hWlength
    terminal_image_volume := hWvolume }⟩⟩

end PoincareConjecture.M47
