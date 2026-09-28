import PoincareConjecture.Proofs.M25.AppA_21_Local.CapChainIntersection
import PoincareConjecture.Proofs.M25.AppA_21_Local.CapChainAttachment
import PoincareConjecture.Proofs.M25.AppA_1_Necks.SeparatingChainTube

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem CapCertificate.exists_cappedTubeCertificate_of_outward_chain :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (C : CapCertificate g) (D : BalancedNeckChain g C.epsilon) {a : ℤ},
      C.epsilon ≤ epsilon0 →
      a ∈ D.shape.active →
      (∀ i ∈ D.shape.active, a ≤ i) →
      D.neck a = C.end_neck →
      (∀ i ∈ D.shape.active, (D.neck i).IsSeparating) →
      (∀ i ∈ D.shape.active, a < i → (D.neck i).center ∉ C.carrier) →
      ∃ K : CappedTubeCertificate g,
        K.cap = C ∧ K.tube.epsilon = C.epsilon ∧ HEq K.tube.chain D ∧
        K.tube.carrier = (⋃ i ∈ D.shape.active, (D.neck i).carrier) ∧
        K.carrier = C.carrier ∪ (⋃ i ∈ D.shape.active, (D.neck i).carrier) := by
  classical
  obtain ⟨epsilon0, hpos, hcap, htube⟩ :=
    BalancedNeckChain.exists_epsilonTubeCertificate_of_separating.{u}
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g C D a he ha hfirst hstart hsep hout
  obtain ⟨T, hTepsilon, hTchain, hTcarrier⟩ :=
    htube D (∅ : Set M) he hsep (empty_subset _)
  have hinter : C.carrier ∩ T.carrier = C.end_neck.carrier := by
    rw [hTcarrier]
    exact C.inter_chain_union_eq_end_neck D ha hfirst hstart hout
  obtain ⟨side, ⟨attachment⟩⟩ := C.exists_attachment_of_inter_eq_end_neck T hinter
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  have himage : T.cylinder.coordinate '' (univ ×ˢ Ioo (0 : ℝ) 1) = T.carrier := by
    apply Subset.antisymm
    · rintro x ⟨z, hz, rfl⟩
      have hm := (T.cylinder.homeomorph (z.1, ⟨z.2, hz.2⟩)).property
      rwa [T.cylinder.coordinate_eq] at hm
    · intro x hx
      exact ⟨T.cylinder.inverse x, T.cylinder.inverse_mem x hx,
        T.cylinder.right_inverse hx⟩
  have hdomain : IsConnected ((univ : Set UnitTwoSphere) ×ˢ Ioo (0 : ℝ) 1) :=
    isConnected_univ.prod (isConnected_Ioo (by norm_num))
  have hTconnected : IsConnected T.carrier := by
    rw [← himage]
    exact hdomain.image T.cylinder.coordinate T.cylinder.coordinate_smooth.continuousOn
  have hmeet : (C.carrier ∩ T.carrier).Nonempty := by
    rw [hinter]
    exact ⟨C.end_neck.center,
      C.end_neck.central_sphere_subset C.end_neck.center_on_central_sphere⟩
  let K : CappedTubeCertificate g :=
    { carrier := C.carrier ∪ T.carrier
      cap := C
      tube := T
      cap_subset := subset_union_left
      tube_subset := subset_union_right
      carrier_eq_union := rfl
      connected := IsConnected.union hmeet C.m25_isConnected_carrier hTconnected
      attachment_side := side
      attachment := attachment }
  exact ⟨K, rfl, hTepsilon, hTchain, hTcarrier,
    congrArg (fun U : Set M => C.carrier ∪ U) hTcarrier⟩

end PoincareConjecture
