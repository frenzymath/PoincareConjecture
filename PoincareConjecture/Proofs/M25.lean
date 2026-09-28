import PoincareConjecture.Statements.M25NeckCapTopology
import PoincareConjecture.Proofs.M25.AppA_1_Necks.SeparatingTube
import PoincareConjecture.Proofs.M25.AppA_1_Necks.SeparationLabels
import PoincareConjecture.Proofs.M25.AppA_20_Fibration
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.CompactCircleProducer
import PoincareConjecture.Proofs.M25.AppA_21_Local
import PoincareConjecture.Proofs.M25.AppA_21_Local.SeparatingNecks
import PoincareConjecture.Proofs.M25.AppA_21_Local.CappedCoreAlternative
import PoincareConjecture.Proofs.M25.AppA_21_Local.NonseparatingLocal
import PoincareConjecture.Proofs.M25.AppA_21_Local.FiniteCappedLocal
import PoincareConjecture.Proofs.M25.AppA_25_Global
import PoincareConjecture.Proofs.M25.Topology3D.Sphere2.Service
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.HorizonSchoenfliesService










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture


































theorem m25NeckCapTopology_of_case_reductions
    (hF : M25.CompactNonseparatingFibrationInput.{u})
    (hII : M25.NonseparatingLocalInput.{u})
    (hI : M25.FiniteCappedLocalInput.{u}) :
    Nonempty RepairedNeckCapTopologyTheory.{u} := by
  classical
  obtain ⟨ε19, h19pos, h19cap, hA19⟩ :=
    NeckOnlyCover.exists_correctedA19Conclusion_of_separating.{u}
  obtain ⟨ε20, h20pos, _, hA20sep⟩ :=
    NeckOnlyCover.exists_correctedA20Conclusion_of_separating.{u}
  obtain ⟨εlab, hlabpos, _, hlabels⟩ :=
    NeckOnlyCover.exists_uniform_separation_labels.{u}
  obtain ⟨εfib, hfibpos, _, hfib⟩ := a20_fibration_of_nonseparating hF
  obtain ⟨εsep, hseppos, _, hIIsep⟩ :=
    ConnectedNeckCapCover.exists_repairedData_of_separating_neck_centers.{u}
  obtain ⟨εII, hIIpos, _, hIInon⟩ := hII
  obtain ⟨εcore, hcorepos, _, hcore⟩ :=
    ConnectedNeckCapCover.exists_repairedData_or_finite_capped_core_frontier.{u}
  obtain ⟨εI, hIpos, _, hI⟩ :=
    hI
  let ε0 : ℝ :=
    min ε19 (min ε20 (min εlab (min εfib (min εsep (min εII (min εcore εI))))))
  have h19 : ε0 ≤ ε19 := min_le_left _ _
  have h20 : ε0 ≤ ε20 := min_le_of_right_le (min_le_left _ _)
  have hlab : ε0 ≤ εlab :=
    min_le_of_right_le (min_le_of_right_le (min_le_left _ _))
  have hfibb : ε0 ≤ εfib :=
    min_le_of_right_le (min_le_of_right_le (min_le_of_right_le (min_le_left _ _)))
  have hsepp : ε0 ≤ εsep :=
    min_le_of_right_le (min_le_of_right_le (min_le_of_right_le
      (min_le_of_right_le (min_le_left _ _))))
  have hIIb : ε0 ≤ εII :=
    min_le_of_right_le (min_le_of_right_le (min_le_of_right_le
      (min_le_of_right_le (min_le_of_right_le (min_le_left _ _)))))
  have hcoreb : ε0 ≤ εcore :=
    min_le_of_right_le (min_le_of_right_le (min_le_of_right_le
      (min_le_of_right_le (min_le_of_right_le (min_le_of_right_le
        (min_le_left _ _))))))
  have hIb : ε0 ≤ εI :=
    min_le_of_right_le (min_le_of_right_le (min_le_of_right_le
      (min_le_of_right_le (min_le_of_right_le (min_le_of_right_le
        (min_le_right _ _))))))
  have hε0pos : 0 < ε0 :=
    lt_min h19pos (lt_min h20pos (lt_min hlabpos (lt_min hfibpos
      (lt_min hseppos (lt_min hIIpos (lt_min hcorepos hIpos))))))

  have ha21 : ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T2Space M] [T3Space M],
      ∀ g : RiemannianMetric 3 M,
        ∀ H : ConnectedNeckCapCover g, H.epsilon ≤ ε0 →
          Nonempty (RepairedNeckCapTopologyData g H) := by
    intro M _ _ _ _ _ _ _ g H he
    by_cases hseed : ∃ x ∈ H.X, ∃ C ∈ H.caps, x ∈ C.core
    ·
      obtain ⟨x, hx, hcap⟩ := hseed
      rcases hcore H (he.trans hcoreb) x hx hcap with hD | hfinite
      · exact hD
      · exact hI H (he.trans hIb) x hx hfinite
    ·
      have hcenters : ∀ x ∈ H.X, ∃ N ∈ H.necks, N.center = x := by
        intro x hx
        rcases H.pointwise_cover x hx with ⟨N, hN, hNx⟩ | ⟨C, hC, hxC⟩
        · exact ⟨N, hN, hNx⟩
        · exact absurd ⟨x, hx, C, hC, hxC⟩ hseed
      by_cases hsep : ∀ N ∈ H.necks, N.center ∈ H.X → N.IsSeparating
      · exact hIIsep H (he.trans hsepp) hcenters hsep
      · obtain ⟨N, hN⟩ := not_forall.mp hsep
        obtain ⟨hN, hN'⟩ := Classical.not_imp.mp hN
        obtain ⟨hNx, hNnot⟩ := Classical.not_imp.mp hN'
        exact hIInon H (he.trans hIIb) hcenters
          ⟨N, hN, hNx, N.m25_isSeparating_or_isNonseparating.resolve_left hNnot⟩
  refine ⟨{
    epsilon₀ := ε0
    epsilon₀_pos := hε0pos
    epsilon₀_le_one_two_hundred := h19.trans h19cap
    a19 := ?_
    a20 := ?_
    a21 := ?_
    a25 := ?_ }⟩
  ·
    intro M _ _ _ _ _ _ _ g H he hsep
    exact hA19 H (he.trans h19) hsep
  ·
    intro M _ _ _ _ _ _ _ g H he hwhole
    rcases hlabels H (he.trans hlab) hwhole with hsep | hnon
    · exact hA20sep H (he.trans h20) hsep hwhole
    · obtain ⟨F, hFcarrier, hFε⟩ := hfib H (he.trans hfibb) hwhole hnon
      exact ⟨CorrectedA20Conclusion.fibration F hFcarrier hFε hnon⟩
  ·
    intro M _ _ _ _ _ _ _ g H he
    exact ha21 g H he
  ·
    intro M _ _ _ _ _ _ _ g H he hwhole
    exact (Classical.choice (ha21 g H he)).globalConclusion hwhole



theorem m25NeckCapTopology : Nonempty RepairedNeckCapTopologyTheory := by
  exact m25NeckCapTopology_of_case_reductions
    M25.compactNonseparatingFibrationInput
    M25.nonseparatingLocalInput_of_local_producers
    (M25.finiteCappedLocalInput_of_services
      M25.Topology3D.schoenfliesService_from_main M25.Topology3D.diffSphereIsotopyService)


theorem m25NeckCapTopologyTheory : Nonempty RepairedNeckCapTopologyTheory :=
  m25NeckCapTopology

end PoincareConjecture
