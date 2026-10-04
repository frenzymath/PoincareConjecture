import PoincareLib.Topology.Manifold.NeckCap.Theory
import PoincareLib.Topology.Manifold.NeckCap.Separation.Tube
import PoincareLib.Topology.Manifold.NeckCap.Separation.Labels
import PoincareLib.Topology.Manifold.NeckCap.Geometry.Fibration
import PoincareLib.Topology.Manifold.NeckCap.Geometry.Fibration.Compact.CompactCircleProducer
import PoincareLib.Topology.Manifold.NeckCap.Geometry.LocalClassification
import PoincareLib.Topology.Manifold.NeckCap.Geometry.LocalClassification.Separating.SeparatingNecks
import PoincareLib.Topology.Manifold.NeckCap.Geometry.LocalClassification.Capped.CappedCoreAlternative
import PoincareLib.Topology.Manifold.NeckCap.Geometry.LocalClassification.Nonseparating.NonseparatingLocal
import PoincareLib.Topology.Manifold.NeckCap.Geometry.LocalClassification.Finite.FiniteCappedLocal
import PoincareLib.Topology.Manifold.NeckCap.Geometry.GlobalClassification
import PoincareLib.Topology.Manifold.NeckCap.SourceServices.Sphere.Service
import PoincareLib.Topology.Manifold.NeckCap.SourceServices.Gluing.SchoenfliesService

/-!
# M25 neck/cap topology proof entry

The numbered theorem assembles the eight-threshold construction from the
proved compact fibration, nonseparating local and finite-capped local
constructors, with the audited Schoenflies and sphere-isotopy services.
Chapter 9 definitions and statement interfaces are frozen.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-
M25: For one universal threshold `0 < epsilon₀ ≤ 1/200`, every sufficiently
small neck/cap cover has the corrected Appendix A outputs: central spheres
separating their own connected component give a balanced epsilon-tube (A.19),
the separating and nonseparating neck-only whole-cover cases give respectively
a tube and an S²-bundle over S¹
(A.20), each connected local cover has one of the six compatible cap/neck
regions (A.21), and a whole cover has one of the four global alternatives
(A.25).  The local output is not promoted to a whole-space conclusion without
the explicit whole-cover hypothesis.

Sources: Morgan--Tian 2007, Definitions 9.72 and 9.77, printed pp. 230--232;
Definition 9.81, printed pp. 234--235; Definitions and Lemmas A.12--A.18,
printed pp. 504--507; Proposition A.19, printed pp. 507--508; Lemma A.20
and Proposition A.21 with Claims A.22--A.24, printed pp. 508--514; and
Proposition A.25, printed p. 514.  Proposition A.19's printed
separating/nonseparating convention and Lemma A.20's branches are corrected by
`MT-NECK-SEPARATION` in
`reviews/errata/2026-09-10-analytic-outline-audit.md`; the same correction is
reflected in `PoincareMT.Statements.Ch09.NeckCapTopology`. The component-relative
interpretation is recorded in
`reviews/errata/2026-09-18-m25-component-separation.md`; unrelated ambient
components cannot establish separation by a neck sphere.
The two-cap and doubly capped tube outputs use the distinct overlap conditions
in Definition 9.81 and A.21/A.25; see
`reviews/errata/2026-09-18-m25-cap-overlap.md`.
The chain's no-return condition excludes a neighborhood of the negative end,
not the entire negative half (Definition 2.18, p. 31, and Definition A.12);
see `reviews/errata/2026-09-18-m25-neck-end.md`.
-/
/-- Assemble the four Appendix A conclusions from the three remaining
case constructions. MT A.19-A.25, pp. 507-514; reviewed entry adoption
of 2026-09-23. The positive threshold is the minimum of eight thresholds. -/
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
  -- A.21 for every small connected cover; reused by A.25.
  have ha21 : ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T2Space M] [T3Space M],
      ∀ g : RiemannianMetric 3 M,
        ∀ H : ConnectedNeckCapCover g, H.epsilon ≤ ε0 →
          Nonempty (RepairedNeckCapTopologyData g H) := by
    intro M _ _ _ _ _ _ _ g H he
    by_cases hseed : ∃ x ∈ H.X, ∃ C ∈ H.caps, x ∈ C.core
    · -- Case I: a point of `H.X` in an input cap core.
      obtain ⟨x, hx, hcap⟩ := hseed
      rcases hcore H (he.trans hcoreb) x hx hcap with hD | hfinite
      · exact hD
      · exact hI H (he.trans hIb) x hx hfinite
    · -- Case II: every point of `H.X` is a cover-neck center.
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
  · -- A.19: the proved separating tube conclusion.
    intro M _ _ _ _ _ _ _ g H he hsep
    exact hA19 H (he.trans h19) hsep
  · -- A.20: uniform labels decide the branch.
    intro M _ _ _ _ _ _ _ g H he hwhole
    rcases hlabels H (he.trans hlab) hwhole with hsep | hnon
    · exact hA20sep H (he.trans h20) hsep hwhole
    · obtain ⟨F, hFcarrier, hFε⟩ := hfib H (he.trans hfibb) hwhole hnon
      exact ⟨CorrectedA20Conclusion.fibration F hFcarrier hFε hnon⟩
  · -- A.21.
    intro M _ _ _ _ _ _ _ g H he
    exact ha21 g H he
  · -- A.25 from the local certificate.
    intro M _ _ _ _ _ _ _ g H he hwhole
    exact (Classical.choice (ha21 g H he)).globalConclusion hwhole

/-- The repaired Appendix A theory, Morgan--Tian A.19-A.25, pp. 507-514,
from the proved local constructions and smooth closed-model services. -/
theorem m25NeckCapTopology : Nonempty RepairedNeckCapTopologyTheory := by
  exact m25NeckCapTopology_of_case_reductions
    M25.compactNonseparatingFibrationInput
    M25.nonseparatingLocalInput_of_local_producers
    (M25.finiteCappedLocalInput_of_services
      M25.Topology3D.schoenfliesService_from_main M25.Topology3D.diffSphereIsotopyService)

/-- The named Appendix A theory exported to downstream milestones. -/
theorem m25NeckCapTopologyTheory : Nonempty RepairedNeckCapTopologyTheory :=
  m25NeckCapTopology

end PoincareMT
