import PoincareConjecture.Proofs.M14.Sec6_5_LocalLipschitzInverse
import PoincareConjecture.Proofs.M14.Sec6_5_LocalLipschitzStableSlice
import PoincareConjecture.Proofs.M14.Sec6_5_LocalLipschitzBranchSmooth
import PoincareConjecture.Proofs.M14.Sec6_5_LocalLipschitzBounds
import PoincareConjecture.Proofs.M14.Sec6_5_LocalLipschitzMinimizers
import PoincareConjecture.Proofs.M14.Sec6_5_LocalLipschitzBranches
import PoincareConjecture.Proofs.M14.Sec6_5_LocalLipschitzTail
import PoincareConjecture.Proofs.M14.Sec6_5_LocalLipschitzSmooth

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}

theorem localLipschitzStatement
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (G : GeneralizedLGeometryTransport n X time I) : M14LocalLipschitzStatement G := by
  intro T τ x E H Z hZ N F0 hN hZN hNtime _hNF0 hmin hRic hgrad
  obtain ⟨CR, hCR, hRic⟩ := hRic
  obtain ⟨Cgrad, hCgrad, hgrad⟩ := hgrad
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  obtain ⟨hsurv, hbij, _⟩ := (H.carrier_exact Z).mp hZ
  obtain ⟨P, hP, hzP, O, hO, hzO, inv, hinv, hmem, hright, hleft⟩ :=
    exists_survivor_local_inverse E hsurv (Real.sqrt_pos.mpr H.tau_pos) hbij
  have hqO : H.endpoint_map Z ∈ O := by
    rwa [← H.endpoint_map_eq Z hZ] at hzO
  have hcenter : inv (H.endpoint_map Z) = (Z, Real.sqrt τ) := by
    rw [H.endpoint_map_eq Z hZ]
    exact hleft _ ⟨hzP, hsurv⟩
  have hmap (q : G.Point) (hq : q ∈ O) : inv q ∈ E.domain ∧ 0 < (inv q).2 :=
    ⟨(hmem q hq).1.2, (hmem q hq).2⟩
  have hclock (q : G.Point) (hq : q ∈ O) :
      (inv q).2 = Real.sqrt (T - G.spacetime.timeFunction q) := by
    have ht := E.clock (inv q).1 (inv q).2 (hmap q hq).1
    rw [hright q hq] at ht
    rw [ht, sub_sub_cancel, Real.sqrt_sq (hmap q hq).2.le]
  have hqtime : 0 < T - G.spacetime.timeFunction (H.endpoint_map Z) := by
    rw [H.endpoint_time Z hZ, sub_sub_cancel]
    exact H.tau_pos
  obtain ⟨ha, hl⟩ := survivorInverse_actions_contMDiffOn hM04 hM12 E hinv hmap
  obtain ⟨B, hB, hqB, hBN, hBO, δ, S, D, hδ, hD, hBclock, hBL⟩ :=
    exists_survivor_action_neighborhood E hN hZN hO hqO hqtime ha.continuousOn hmap hright
  obtain ⟨C, hC, hpaths⟩ := exists_confined_minimizers_with_uniform_square_speed
    hCoordinates hM12 hδ hD hCR hCgrad hBclock
    (fun q hq => hmin q (hBN hq)) hBL hRic hgrad
  obtain ⟨V, hV, hqV, J, hJ, hsJ, hcapture⟩ :=
    exists_stable_slice_neighborhood E H hZ hP hzP
  obtain ⟨A, hA, hqA, htail⟩ := exists_terminal_tail_neighborhood (x := x)
    H.tau_pos (H.endpoint_time Z hZ) (hV.mem_nhds hqV) hC
  have hcarrier : IsOpen (O ∩ (fun q => (inv q).1) ⁻¹' H.carrier) :=
    hinv.continuousOn.fst.isOpen_inter_preimage hO H.carrier_open
  have ht : ContMDiff (spacetimeModel n) 𝓘(ℝ) ∞ G.spacetime.timeFunction :=
    G.spacetime.time_smooth
  have hc : Continuous (fun q : G.Point => Real.sqrt (T - G.spacetime.timeFunction q)) :=
    Real.continuous_sqrt.comp (continuous_const.sub ht.continuous)
  let U := ((B ∩ (O ∩ (fun q => (inv q).1) ⁻¹' H.carrier)) ∩ A) ∩
    (fun q => Real.sqrt (T - G.spacetime.timeFunction q)) ⁻¹' J
  have hU : IsOpen U := ((hB.inter hcarrier).inter hA).inter (hJ.preimage hc)
  have hqU : H.endpoint_map Z ∈ U := by
    refine ⟨⟨⟨hqB, hqO, ?_⟩, hqA⟩, ?_⟩
    · change (inv (H.endpoint_map Z)).1 ∈ H.carrier
      simpa only [hcenter] using hZ
    · change Real.sqrt (T - G.spacetime.timeFunction (H.endpoint_map Z)) ∈ J
      simpa only [H.endpoint_time Z hZ, sub_sub_cancel] using hsJ
  have hUO : U ⊆ O := fun _ hq => hBO hq.1.1.1
  have heq : EqOn (M14ReducedLengthAt G T 0 x)
      (fun q => E.action (inv q).1 (inv q).2 / (2 * (inv q).2)) U := by
    intro q hq
    change M14ReducedLengthAt G T 0 x q = E.action (inv q).1 (inv q).2 / (2 * (inv q).2)
    have hqO' := hUO hq
    have hqB' := hq.1.1.1
    have hs := (hmap q hqO').2
    have hsurv' := (hmap q hqO').1
    have hbpos : 0 < T - G.spacetime.timeFunction q := hNtime (hBN hqB')
    by_cases hfuture : τ < T - G.spacetime.timeFunction q
    · obtain ⟨p, hp, R, ER, hEuler, henergy⟩ := hpaths q hqB'
      have hpV : p.curve τ ∈ V := htail q hq.1.2 p R henergy hfuture
      have hptime : G.spacetime.timeFunction (p.curve τ) = T - τ :=
        p.curve_time τ ⟨H.tau_pos.le, hfuture.le⟩
      obtain ⟨W, hW, hWP, hWeq⟩ := hcapture (p.curve τ) hpV hptime _ hq.2
      obtain ⟨W0, hW0, hcurve⟩ := exists_exponential_branch_of_square_euler E R ER hEuler
      have hW0eq : W0 = W := initialVector_eq_of_minimizing_stable_prefix hM12 E H hW
        p hp hW0 hfuture hcurve hWeq.symm
      subst W0
      have hpoint : E.gamma W (Real.sqrt (T - G.spacetime.timeFunction q)) = q :=
        (hcurve ⟨p.tau_lt.le, le_rfl⟩).symm.trans p.curve_end
      have hinvq : inv q = (W, Real.sqrt (T - G.spacetime.timeFunction q)) := by
        have h := hleft _ ⟨hWP, hW0⟩
        rwa [hpoint] at h
      have haction := action_eq_exponentialAction_of_curve_eqOn E p hW0
        (Real.sqrt_pos.mpr p.tau_lt) hpoint hcurve
      unfold M14ReducedLengthAt
      rw [reducedLengthValue_eq_of_minimizing p hp, haction, hinvq]
    · have hstime : (inv q).2 ^ 2 ≤ τ := by
        rw [hclock q hqO', Real.sq_sqrt hbpos.le]
        exact le_of_not_gt hfuture
      have hp := exponentialPath_minimizing_of_stable_prefix hCoordinates hM04 hM12 E H
        hq.1.1.2.2 hs hstime hsurv'
      exact (congrArg (M14ReducedLengthAt G T 0 x) (hright q hqO')).symm.trans
        (reducedLengthAt_exponential_of_minimizing E hsurv' hs hp)
  have hsmooth : ContMDiffAt (spacetimeModel n) 𝓘(ℝ) 1 (M14ReducedLengthAt G T 0 x)
      (H.endpoint_map Z) :=
    (((hl.mono hUO).congr heq).contMDiffAt (hU.mem_nhds hqU)).of_le (by simp)
  exact exists_chartProductLipschitzOn_of_contMDiffAt hsmooth (hN.mem_nhds hZN)

end PoincareConjecture.M14
