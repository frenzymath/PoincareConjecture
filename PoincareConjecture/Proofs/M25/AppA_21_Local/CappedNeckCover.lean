import PoincareConjecture.Proofs.M25.AppA_21_Local.CappedNeckExhaustion
import PoincareConjecture.Proofs.M25.AppA_21_Local.CappedChainTube
import PoincareConjecture.Definitions.M25NeckCapTopology

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem ConnectedNeckCapCover.exists_repairedData_of_cap_and_neck_centers :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (H : ConnectedNeckCapCover g), H.epsilon ≤ epsilon0 →
      ∀ (C : CapCertificate g), C ∈ H.caps →
      (H.X ∩ C.carrier).Nonempty →
      (∀ x ∈ H.X \ C.carrier, ∃ N ∈ H.necks, N.center = x) →
      Nonempty (RepairedNeckCapTopologyData g H) := by
  classical
  obtain ⟨epsilonE, hE, hEcap, hexhaust⟩ :=
    CapCertificate.exists_covering_outward_chain.{u}
  obtain ⟨epsilonT, hT, _, htube⟩ :=
    CapCertificate.exists_cappedTubeCertificate_of_outward_chain.{u}
  refine ⟨min epsilonE epsilonT, lt_min hE hT,
    (min_le_left _ _).trans hEcap, ?_⟩
  intro M _ _ _ _ _ _ g H he C hC hmeet hcover
  have hCe : C.epsilon = H.epsilon := H.cap_epsilon C hC
  by_cases hsingle : H.X ⊆ C.carrier
  · refine ⟨{ region := .singleCap C hsingle, compatible := ?_ }⟩
    exact ⟨hCe, H.cap_constant_bound C hC⟩
  let S : Set (EpsilonNeck g) := insert C.end_neck H.necks
  have hS : ∀ N ∈ S, N.epsilon = C.epsilon := by
    intro N hN
    rcases mem_insert_iff.mp hN with rfl | hN
    · exact C.end_neck_epsilon
    · exact (H.neck_epsilon N hN).trans hCe.symm
  have hcenter : ∀ x ∈ H.X \ C.carrier, ∃ N ∈ S, N.center = x := by
    intro x hx
    obtain ⟨N, hN, hNx⟩ := hcover x hx
    exact ⟨N, mem_insert_of_mem _ hN, hNx⟩
  have hsmallE : C.epsilon ≤ epsilonE := by
    rw [hCe]
    exact he.trans (min_le_left _ _)
  obtain ⟨D, _, hstart, hshape, hsep, hcenters, _, _, hXD⟩ :=
    hexhaust C S H.X hsmallE (mem_insert _ _) hS
      H.connected_X.isPreconnected hmeet hcenter
  have hfirst : (0 : ℤ) ∈ D.shape.active ∧
      ∀ i ∈ D.shape.active, 0 ≤ i := by
    rcases hshape with ⟨b, hb, hs⟩ | hs
    · rw [hs]
      change ((0 : ℤ) ≤ 0 ∧ 0 ≤ b) ∧ ∀ i ∈ Icc (0 : ℤ) b, 0 ≤ i
      exact ⟨⟨le_rfl, hb⟩, fun _ hi => hi.1⟩
    · rw [hs]
      change (0 : ℤ) ≤ 0 ∧ ∀ i ∈ Ici (0 : ℤ), 0 ≤ i
      exact ⟨le_rfl, fun _ hi => hi⟩
  have hsmallT : C.epsilon ≤ epsilonT := by
    rw [hCe]
    exact he.trans (min_le_right _ _)
  obtain ⟨K, hKC, hKe, _, _, hKcarrier⟩ :=
    htube C D hsmallT hfirst.1 hfirst.2 hstart hsep
      (fun i hi hi0 => (hcenters i hi hi0).2)
  have hXK : H.X ⊆ K.carrier := by
    rw [hKcarrier]
    exact hXD
  refine ⟨{ region := .cappedTube K hXK, compatible := ?_ }⟩
  exact ⟨by simpa only [hKC] using hCe, hKe.trans hCe,
    by simpa only [hKC] using H.cap_constant_bound C hC, ⟨K.attachment⟩⟩

end PoincareConjecture
