import PoincareConjecture.Proofs.M47.LimitFiniteControlledInterior
import PoincareConjecture.Proofs.M47.LimitNoncollapseFiniteHarnackDomain
import PoincareConjecture.Proofs.M47.LimitNoncollapsePhysicalTime
import PoincareConjecture.Proofs.M47.TerminalCommonIntervalHorizon
import PoincareConjecture.Proofs.M34.Standard.GeneralizedReverseBall
import PoincareConjecture.Proofs.M04.ShiCarrier











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M47

variable (F : ℕ → SurgeryFlowData.{u}) (W : ∀ k, M33RegularHistoryWindow (F k))
  (history : ∀ k, M33RegularHistoryData (W k)) (t : ℕ → ℝ)
  (ht : ∀ k, t k ∈ (history k).generalized.interval)
  (x : ∀ k, ((history k).generalized.slice (t k)).carrier)
  (hPositive : ∀ k, 0 < ((F k).connection (t k)).scalarCurvature
    ((history k).history.forward (t k) (ht k) (x k)))
  (hDiverges : Tendsto (fun k => ((F k).connection (t k)).scalarCurvature
    ((history k).history.forward (t k) (ht k) (x k))) atTop atTop)

local notation "V" => regularHistoryBlowupSequence F W history t ht x hPositive hDiverges

variable {H : ℝ≥0∞} (G : GeneralizedBlowupConvergence
  (regularHistoryBlowupSequence F W history t ht x hPositive hDiverges)
  (blowupBackwardInterval H))

private local instance longerSlabTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance longerSlabCharts : ChartedSpace
    (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance longerSlabManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold



theorem limitFinite_slab_of_preserved_sources
    (hfinite : H ≠ ⊤) (rho : ℕ → ℕ) (hrho : StrictMono rho)
    {T B : ℝ} (hT : 0 < T) (hB : 0 ≤ B)
    (sources : ∀ R : ℝ, 0 < R → ∀ err : ℝ, 0 < err →
      let U := (G.limit.flow.metric 0).ball G.limit.base R
      ∀ᶠ k : ℕ in atTop, U ⊆ G.exhaustion.space (rho k) ∧
        ∃ b : ℝ, b < -T ∧
          ∃ E : SurgeryFlowCylinder (F (G.subsequence (rho k))) G.limit.sliceCarrier
              (t (G.subsequence (rho k))) ((V).scale (G.subsequence (rho k)))
              (Icc b 0) U,
            (∀ s (_hs : s ∈ Icc (-H.toReal) 0)
              (hsG : s ∈ Icc (-G.exhaustion.time (rho k)) 0)
              (hsE : s ∈ Icc b 0), ∀ z ∈ U,
                E.forward s hsE z = (history (G.subsequence (rho k))).history.forward
                  (t (G.subsequence (rho k)) + s / (V).scale (G.subsequence (rho k)))
                  (limitNoncollapse_physical_time_mem G (rho k) s hsG)
                  ((G.embedding (rho k)).forward s hsG z)) ∧
            (∀ s hs z, z ∈ U →
              |((F (G.subsequence (rho k))).connection
                (t (G.subsequence (rho k)) +
                  s / (V).scale (G.subsequence (rho k)))).curvatureTensorNorm
                  (E.forward s hs z)| ≤ B * (V).scale (G.subsequence (rho k))) ∧
            (∀ s hs z, z ∈ U →
              ((F (G.subsequence (rho k))).connection
                (t (G.subsequence (rho k)) +
                  s / (V).scale (G.subsequence (rho k)))).negativeCurvaturePart
                  (E.forward s hs z) ≤ err * (V).scale (G.subsequence (rho k)))) :
    TerminalCommonIntervalSlab
      (terminalCommonInterval_reindex V (G.subsequence ∘ rho)
        (G.subsequence_strictMono.comp hrho)) T := by
  let : T2Space G.limit.carrier.carrier := G.limit.carrier.t2Space
  refine ⟨B, hB, fun A hA err herr => ?_⟩
  have hcapture := hrho.tendsto_atTop.eventually
    (G.eventually_source_ball_localization_zero A hA)
  filter_upwards [sources (2 * A) (by positivity) err herr, hcapture] with k hk hcap
  obtain ⟨hspace, b, hb, E, hmap, hnorm, hnegative⟩ := hk
  let U := (G.limit.flow.metric 0).ball G.limit.base (2 * A)
  have hU : IsOpen U := M04.initial_ball_isOpen _ _ _
  let e0 := (G.embedding (rho k)).restrict (Subset.refl _) hspace
  have zero : (0 : ℝ) ∈ Icc (-G.exhaustion.time (rho k)) 0 :=
    ⟨neg_nonpos.mpr (G.exhaustion.time_pos (rho k)).le, le_rfl⟩
  have hfuture : ∀ s (hs : s ∈ Icc (-G.exhaustion.time (rho k)) 0)
      (hsE : s ∈ Icc b 0), ∀ z ∈ U,
        E.forward s hsE z = (history (G.subsequence (rho k))).history.forward
          (t (G.subsequence (rho k)) + s / (V).scale (G.subsequence (rho k)))
          (((history (G.subsequence (rho k))).generalized.slice_nonempty_iff _).mp
            ⟨e0.forward s hs z⟩) (e0.forward s hs z) := by
    intro s hs hsE z hz
    have hdomain := G.exhaustion.time_subset (rho k) hs
    rw [limitFinite_domain_eq hfinite] at hdomain
    exact hmap s ⟨hdomain.1.le, hdomain.2⟩ hs hsE z hz
  have captured : ∀ y ∈ (V).baseBall (G.subsequence (rho k)) A,
      ∃ z ∈ U, e0.pointMap 0 zero z =
        (⟨t (G.subsequence (rho k)), y⟩ :
          (history (G.subsequence (rho k))).generalized.point) := by
    intro y hy
    obtain ⟨z, hz, hzero, hpoint⟩ := hcap y hy
    exact ⟨z, hz.1, hpoint⟩
  exact terminalCommonInterval_reindex_cylinder_iff.mpr
    (limitFinite_controlled_of_preserved_interior F W history t ht x hPositive hDiverges
      (G.subsequence (rho k)) hT hb hU E e0 zero hfuture hnorm hnegative captured)



theorem limitFinite_longer_slab_false
    {D : GeneralizedBlowupSequence.{u}} (hdec : TerminalCommonIntervalDecided D)
    {rho : ℕ → ℕ} (hrho : StrictMono rho) {T : ℝ}
    (hlarge : terminalCommonIntervalHorizon D < ENNReal.ofReal T)
    (hslab : TerminalCommonIntervalSlab (terminalCommonInterval_reindex D rho hrho) T) :
    False := by
  have hT : 0 < T := ENNReal.ofReal_pos.mp (bot_le.trans_lt hlarge)
  have hmem : ENNReal.ofReal T ∈ TerminalCommonIntervalHorizons
      (terminalCommonInterval_reindex D rho hrho) := by
    intro t _ht htT
    apply terminalCommonInterval_slab_mono hslab
    exact ((ENNReal.ofReal_lt_ofReal_iff hT).mp htT).le
  have hle : ENNReal.ofReal T ≤ terminalCommonIntervalHorizon
      (terminalCommonInterval_reindex D rho hrho) := le_sSup hmem
  rw [terminalCommonInterval_horizon_reindex hdec hrho] at hle
  exact (not_lt_of_ge hle) hlarge

end PoincareConjecture.M47
