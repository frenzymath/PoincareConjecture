import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_4_ActualPhaseRestart
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_4_PhaseContinuity
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_4_RestartPasting

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Topology Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M46

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

theorem exponential_survival_of_phase_cluster
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) (Z : G.Horizontal x)
    {sk : ℕ → ℝ} {s : ℝ} (hs : 0 < s) (hsk : Tendsto sk atTop (𝓝 s))
    (hsurv : ∀ k, (Z, sk k) ∈ E.domain)
    (hbelow : ∀ᶠ k in atTop, 0 < sk k ∧ sk k < s)
    (z : TotalSpace (EuclideanSpace ℝ (Fin n)) G.Horizontal)
    (hcluster : MapClusterPt z atTop (fun k => exponentialPhase E Z (sk k))) :
    ∃ r : ℝ, s ≤ r ∧
      Icc 0 r ∈ 𝓝[{w | 0 ≤ w ∧ T - w ^ 2 ∈ I.domain}] s ∧
      (Z, r) ∈ E.domain := by
  have htime : Continuous G.spacetime.timeFunction :=
    (show ContMDiff (spacetimeModel n) 𝓘(ℝ, ℝ) ∞ G.spacetime.timeFunction
      from G.spacetime.time_smooth).continuous
  have hphaseTime : Continuous
      (fun z : TotalSpace (EuclideanSpace ℝ (Fin n)) G.Horizontal =>
        G.spacetime.timeFunction z.proj) :=
    htime.comp (FiberBundle.continuous_proj _ _)
  have hclockCluster := hcluster.continuousAt_comp hphaseTime.continuousAt
  have hclockLimit : Tendsto
      (fun k => G.spacetime.timeFunction (exponentialPhase E Z (sk k)).proj)
      atTop (𝓝 (T - s ^ 2)) := by
    have heq : (fun k => G.spacetime.timeFunction (exponentialPhase E Z (sk k)).proj) =
        fun k => T - (sk k) ^ 2 := funext (fun k => E.clock Z (sk k) (hsurv k))
    rw [heq]
    exact tendsto_const_nhds.sub (hsk.pow 2)
  have hclock : G.spacetime.timeFunction z.proj = T - s ^ 2 :=
    eq_of_nhds_neBot (hclockCluster.clusterPt.mono hclockLimit).neBot
  have hT : T ∈ I.domain := by
    rw [← G.spacetime.time_range]
    exact ⟨x, E.base_time⟩
  obtain ⟨l, r, hl, hls, hsr, hnear, hrestart⟩ :=
    exists_actualPhase_uniform_restart hM04 hM12 hT hs z hclock
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_prod_iff.mp hrestart
  have hskWithin : Tendsto sk atTop
      (𝓝[{w | 0 ≤ w ∧ T - w ^ 2 ∈ I.domain}] s) :=
    tendsto_nhdsWithin_iff.mpr ⟨hsk, Eventually.of_forall (fun k => E.domain_admissible (hsurv k))⟩
  have hAevent := hskWithin.eventually hA
  have hlevent : ∀ᶠ k in atTop, l < sk k := hsk.eventually (Ioi_mem_nhds hls)
  obtain ⟨k, hBk, hAk, hlk, hkpos, hks⟩ :=
    ((hcluster.frequently hB).and_eventually (hAevent.and (hlevent.and hbelow))).exists
  obtain ⟨q₀, q₁, p, R, extension, hEuler, hpoint, hvel⟩ :=
    (hAB (show (sk k, exponentialPhase E Z (sk k)) ∈ A ×ˢ B from ⟨hAk, hBk⟩)).2
      (E.clock Z (sk k) (hsurv k))
  let P : M14SquareRootInitialValuePath G T ((sk k) ^ 2) x (E.gamma Z (sk k)) Z := {
    path := E.path Z (sk k) (hsurv k) hkpos
    square_path := E.square_path Z (sk k) (hsurv k) hkpos
    extension := E.square_extension Z (sk k) (hsurv k) hkpos
    euler := E.square_euler Z (sk k) (hsurv k) hkpos
    initial_velocity := E.square_initial_velocity Z (sk k) (hsurv k) hkpos
  }
  have hphase := exponentialPhase_eq_squarePath E (hsurv k) hkpos
  have hpointP : (exponentialPhase E Z (sk k)).proj = P.square_path.curve (sk k) :=
    congrArg TotalSpace.proj hphase
  have hvelP : HEq (exponentialPhase E Z (sk k)).2
      (P.square_path.horizontal_velocity (sk k)) := (TotalSpace.ext_iff.mp hphase).2
  obtain ⟨q, Q, _⟩ := exists_initialValuePath_of_matching_restart hM04 hM12 hl.le hlk
    (hks.trans_le hsr) P R extension hEuler (hpoint.trans hpointP) (hvel.trans hvelP)
  exact ⟨r, hsr, mem_of_superset hnear (Icc_subset_Icc hl.le le_rfl),
    (E.positive_survival_iff Z r (hs.trans_le hsr)).mpr ⟨q, ⟨Q⟩⟩⟩

end PoincareConjecture.Proofs.M46
