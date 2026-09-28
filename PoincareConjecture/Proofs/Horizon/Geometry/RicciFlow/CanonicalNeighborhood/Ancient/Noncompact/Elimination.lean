import PoincareConjecture.Statements.M26CanonicalNeighborhoods
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Calibration
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls














set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M]
  {g : RiemannianMetric 3 M}


theorem CapCertificate.isCompact_univ_of_whole (cap : CapCertificate g)
    (hcomplete : MetricComplete g) (hwhole : Set.univ ⊆ cap.carrier) :
    IsCompact (Set.univ : Set M) := by
  obtain ⟨p, _⟩ := cap.core_nonempty
  let R := cap.cap_constant *
    scalarCurvatureSupOn g cap.connection cap.carrier ^ (-1 / 2 : ℝ)
  have hball : {q | g.edist p q ≤ ENNReal.ofReal R} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    have hdiam : intrinsicEDist g cap.carrier p q ≤
        intrinsicDiameter g cap.carrier :=
      le_sSup ⟨(⟨p, hwhole (Set.mem_univ p)⟩, ⟨q, hwhole (Set.mem_univ q)⟩), rfl⟩
    exact ((g.edist_le_intrinsicEDist cap.carrier p q).trans hdiam).trans
      cap.intrinsic_diameter_bound.le
  rw [← hball]
  exact g.isCompact_closedBall_of_metricComplete hcomplete p R



theorem GlobalNeckCapConclusion.tube_or_capped_of_noncompact
    {epsilon C : ℝ} (conclusion : GlobalNeckCapConclusion g epsilon C)
    (hcomplete : MetricComplete g) (hnoncompact : ¬ IsCompact (Set.univ : Set M)) :
    (∃ tube : EpsilonTubeCertificate g Set.univ,
      tube.epsilon = epsilon ∧ tube.carrier = Set.univ) ∨
    (∃ tube : CappedTubeCertificate g,
      tube.carrier = Set.univ ∧ tube.cap.epsilon = epsilon ∧
      tube.tube.epsilon = epsilon ∧ tube.cap.cap_constant ≤ C) := by
  cases conclusion with
  | closed Y kind component whole shape =>
      exact (hnoncompact (by
        simpa only [Set.eq_univ_of_univ_subset whole] using component.compact)).elim
  | noncompact certificate =>
      rcases certificate.shape with ⟨cap, hcarrier, hepsilon, hconstant, hkind⟩ |
        ⟨tube, hcarrier, hepsilon, htube, hconstant, hkind⟩
      · exact (hnoncompact (cap.isCompact_univ_of_whole hcomplete
          (by simpa only [hcarrier] using certificate.whole))).elim
      · exact Or.inr ⟨tube, hcarrier.trans (Set.eq_univ_of_univ_subset certificate.whole),
          hepsilon, htube, hconstant⟩
  | tube tube hepsilon hcarrier =>
      exact Or.inl ⟨tube, hepsilon, hcarrier⟩
  | fibration fibration hepsilon hcarrier =>
      exact (hnoncompact (by simpa only [hcarrier] using fibration.compact)).elim

end PoincareConjecture
