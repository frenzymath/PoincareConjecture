import PoincareConjecture.Proofs.M25.AppA_21_Local.CapTruncationChoice
import PoincareConjecture.Proofs.M25.AppA_21_Local.CappedStoppingChoice
import PoincareConjecture.Proofs.M25.AppA_21_Local.CappedChainTube
import PoincareConjecture.Proofs.M25.AppA_21_Local.CapCoreContact
import PoincareConjecture.Definitions.M25NeckCapTopology










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture




theorem ConnectedNeckCapCover.exists_repairedData_or_finite_capped_core_frontier :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (H : ConnectedNeckCapCover g), H.epsilon ≤ epsilon0 →
      ∀ (x : M), x ∈ H.X → (∃ C ∈ H.caps, x ∈ C.core) →
      Nonempty (RepairedNeckCapTopologyData g H) ∨
      (∃ C0 ∈ H.caps, x ∈ C0.core ∧
        (∀ C1 ∈ H.caps,
          ¬ (C0.carrier \ C0.end_neck.region (H.epsilon⁻¹ / 2) H.epsilon⁻¹ ⊆
            C1.core)) ∧
        ∃ (b : ℤ) (D : BalancedNeckChain g C0.epsilon),
          0 ≤ b ∧ D.shape = ChainShape.finite 0 b ∧
          D.source_necks = insert C0.end_neck H.necks ∧ D.neck 0 = C0.end_neck ∧
          (∀ i ∈ D.shape.active, (D.neck i).IsSeparating) ∧
          (∀ i ∈ D.shape.active, 0 < i →
            (D.neck i).center ∈ H.X \ C0.carrier) ∧
          (∀ i ∈ D.shape.active, i + 1 ∈ D.shape.active →
            closure ((D.neck i).region (C0.epsilon⁻¹ / 2) C0.epsilon⁻¹) ⊆
                (D.neck (i + 1)).carrier ∧
              closure ((D.neck (i + 1)).region
                  (-C0.epsilon⁻¹) (-C0.epsilon⁻¹ / 2)) ⊆ (D.neck i).carrier) ∧
          (∀ i ∈ D.shape.active, i + 1 ∈ D.shape.active →
            (D.neck (i + 1)).center ∈ closure ((D.neck i).region 0 C0.epsilon⁻¹) ∧
              (D.neck (i + 1)).center ∉ (D.neck i).carrier) ∧
          ∃ K : CappedTubeCertificate g,
            K.cap = C0 ∧ K.tube.epsilon = H.epsilon ∧ HEq K.tube.chain D ∧
            K.tube.carrier = (⋃ i ∈ D.shape.active, (D.neck i).carrier) ∧
            K.carrier = C0.carrier ∪ (⋃ i ∈ D.shape.active, (D.neck i).carrier) ∧
            ∃ C1 ∈ H.caps, ∃ y ∈ H.X,
              y ∈ C1.core ∧ y ∉ K.carrier ∧
              y ∈ closure ((D.neck b).region 0 C0.epsilon⁻¹) ∧
              (K.carrier ∩ C1.boundary_sphere).Nonempty) := by
  classical
  obtain ⟨epsilonA, hA, hAcap, hchoice⟩ :=
    ConnectedNeckCapCover.exists_singleCap_or_core_cap_without_enlarging_truncation.{u}
  obtain ⟨epsilonS, hS, _, hstop⟩ :=
    ConnectedNeckCapCover.exists_outward_cappedTube_or_core_frontier.{u}
  obtain ⟨epsilonT, hT, _, htube⟩ :=
    CapCertificate.exists_cappedTubeCertificate_of_outward_chain.{u}
  refine ⟨min epsilonA (min epsilonS epsilonT), lt_min hA (lt_min hS hT),
    (min_le_left _ _).trans hAcap, ?_⟩
  intro M _ _ _ _ _ _ g H hepsilon x hx hseed
  rcases hchoice H (hepsilon.trans (min_le_left _ _)) x hx hseed with
      ⟨C, _, hXC, hcompatible⟩ | ⟨C0, hC0, hx0, hno⟩
  · exact Or.inl ⟨{ region := .singleCap C hXC, compatible := hcompatible }⟩
  have hCe : C0.epsilon = H.epsilon := H.cap_epsilon C0 hC0
  have hmeet : (H.X ∩ C0.carrier).Nonempty :=
    ⟨x, hx, C0.m25_core_subset_carrier hx0⟩
  have heS : H.epsilon ≤ epsilonS :=
    hepsilon.trans ((min_le_right _ _).trans (min_le_left _ _))
  rcases hstop H heS C0 hC0 hmeet with ⟨K, hKcap, hKe, hXK⟩ | hfinite
  · refine Or.inl ⟨{ region := .cappedTube K hXK, compatible := ?_ }⟩
    exact ⟨by simpa only [hKcap] using hCe, hKe,
      by simpa only [hKcap] using H.cap_constant_bound C0 hC0, ⟨K.attachment⟩⟩
  obtain ⟨b, D, hb, hshape, hsource, hstart, hsep, hcenters, hquarters,
    hincidence, C1, hC1, y, hyX, hycore, hyout, hyfront⟩ := hfinite
  have hzero : (0 : ℤ) ∈ D.shape.active := by
    rw [hshape]
    exact ⟨le_rfl, hb⟩
  have hfirst : ∀ i ∈ D.shape.active, (0 : ℤ) ≤ i := by
    intro i hi
    rw [hshape] at hi
    exact hi.1
  have hbactive : b ∈ D.shape.active := by
    rw [hshape]
    exact ⟨hb, le_rfl⟩
  have heT : C0.epsilon ≤ epsilonT := by
    rw [hCe]
    exact hepsilon.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨K, hKcap, hKe, hKchain, hKtube, hKcarrier⟩ :=
    htube C0 D heT hzero hfirst hstart hsep
      (fun i hi hi0 => (hcenters i hi hi0).2)
  have hpositive : (D.neck b).region 0 C0.epsilon⁻¹ ⊆ K.carrier := by
    intro z hz
    rw [hKcarrier]
    exact Or.inr (mem_iUnion₂.mpr ⟨b, hbactive, hz.1⟩)
  have hcontact : (closure K.carrier ∩ C1.core).Nonempty :=
    ⟨y, closure_mono hpositive hyfront, hycore⟩
  have hnoK : ¬ (K.cap.carrier \
      K.cap.end_neck.region (K.cap.epsilon⁻¹ / 2) K.cap.epsilon⁻¹ ⊆ C1.core) := by
    simpa only [hKcap, hCe] using hno C1 hC1
  have hboundary : (K.carrier ∩ C1.boundary_sphere).Nonempty :=
    K.exists_boundary_point_of_core_contact C1 hcontact hnoK
  have hyK : y ∉ K.carrier := by simpa only [hKcarrier] using hyout
  exact Or.inr ⟨C0, hC0, hx0, hno, b, D, hb, hshape, hsource, hstart,
    hsep, hcenters, hquarters, hincidence, K, hKcap, hKe.trans hCe, hKchain,
    hKtube, hKcarrier, C1, hC1, y, hyX, hycore, hyK, hyfront, hboundary⟩

end PoincareConjecture
