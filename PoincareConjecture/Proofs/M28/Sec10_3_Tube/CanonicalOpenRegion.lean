import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CanonicalCarrierUnion
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.OpenCapRestriction
import PoincareConjecture.Proofs.M03.ConnectionExistence
import PoincareConjecture.Statements.M25NeckCapTopology










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology Bundle

universe u

namespace PoincareConjecture.ConnectedNeckCapCover

open M28

variable {M : Type u} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  {g : RiemannianMetric 3 M}


def canonicalOpenSet (H : ConnectedNeckCapCover g) : TopologicalSpace.Opens M :=
  ⟨H.canonicalCarrierUnion, H.isOpen_canonicalCarrierUnion⟩

variable [SecondCountableTopology M]



def restrictToCanonicalUnion (H : ConnectedNeckCapCover g)
    (DV : LeviCivitaData (intrinsicOpenMetric g H.canonicalOpenSet)) :
    ConnectedNeckCapCover (intrinsicOpenMetric g H.canonicalOpenSet) := by
  let V := H.canonicalOpenSet
  let neck (N : {N : EpsilonNeck g // N ∈ H.necks ∧ N.center ∈ H.X}) :=
    N.val.restrictOpen V
      (fun _ hx => Or.inl ⟨N.val, N.property.1, N.property.2, hx⟩) DV
  let cap (N : {N : CapCertificate g // N ∈ H.caps ∧ (N.core ∩ H.X).Nonempty}) :=
    N.val.restrictOpen V
      (fun _ hx => Or.inr ⟨N.val, N.property.1, N.property.2, hx⟩) DV
  exact {
    epsilon := H.epsilon
    epsilon_pos := H.epsilon_pos
    epsilon_threshold := H.epsilon_threshold
    epsilon_threshold_pos := H.epsilon_threshold_pos
    epsilon_threshold_le_one_two_hundred := H.epsilon_threshold_le_one_two_hundred
    epsilon_le_threshold := H.epsilon_le_threshold
    cap_constant := H.cap_constant
    cap_constant_pos := H.cap_constant_pos
    X := (Subtype.val : V → M) ⁻¹' H.X
    connected_X := H.connected_X.preimage_of_isOpenMap Subtype.val_injective
      V.isOpen.isOpenEmbedding_subtypeVal.isOpenMap (by
        intro x hx
        exact ⟨⟨x, H.subset_canonicalCarrierUnion hx⟩, rfl⟩)
    necks := range neck
    caps := range cap
    pointwise_cover := by
      intro x hx
      rcases H.pointwise_cover (x : M) hx with ⟨N, hN, hcenter⟩ | ⟨N, hN, hcore⟩
      · let n : {N : EpsilonNeck g // N ∈ H.necks ∧ N.center ∈ H.X} :=
          ⟨N, hN, hcenter ▸ hx⟩
        exact Or.inl ⟨neck n, mem_range_self n, Subtype.ext hcenter⟩
      · let n : {N : CapCertificate g // N ∈ H.caps ∧ (N.core ∩ H.X).Nonempty} :=
          ⟨N, hN, ⟨x, hcore, hx⟩⟩
        exact Or.inr ⟨cap n, mem_range_self n, hcore⟩
    neck_epsilon := by
      rintro _ ⟨N, rfl⟩
      exact H.neck_epsilon N.val N.property.1
    cap_epsilon := by
      rintro _ ⟨N, rfl⟩
      exact H.cap_epsilon N.val N.property.1
    cap_constant_bound := by
      rintro _ ⟨N, rfl⟩
      exact H.cap_constant_bound N.val N.property.1 }


@[simp] theorem restrictToCanonicalUnion_epsilon (H : ConnectedNeckCapCover g)
    (DV : LeviCivitaData (intrinsicOpenMetric g H.canonicalOpenSet)) :
    (H.restrictToCanonicalUnion DV).epsilon = H.epsilon := rfl


@[simp] theorem restrictToCanonicalUnion_cap_constant (H : ConnectedNeckCapCover g)
    (DV : LeviCivitaData (intrinsicOpenMetric g H.canonicalOpenSet)) :
    (H.restrictToCanonicalUnion DV).cap_constant = H.cap_constant := rfl


@[simp] theorem restrictToCanonicalUnion_X (H : ConnectedNeckCapCover g)
    (DV : LeviCivitaData (intrinsicOpenMetric g H.canonicalOpenSet)) :
    (H.restrictToCanonicalUnion DV).X =
      (Subtype.val : H.canonicalOpenSet → M) ⁻¹' H.X := rfl

variable [T2Space M]



def canonicalOpenConnection (H : ConnectedNeckCapCover g) :
    LeviCivitaData (intrinsicOpenMetric g H.canonicalOpenSet) :=
  Classical.choice (exists_leviCivitaData (intrinsicOpenMetric g H.canonicalOpenSet))



def canonicalOpenTopology (H : ConnectedNeckCapCover g)
    (P : RepairedNeckCapTopologyTheory.{u}) (hsmall : H.epsilon ≤ P.epsilon₀) :
    RepairedNeckCapTopologyData (intrinsicOpenMetric g H.canonicalOpenSet)
      (H.restrictToCanonicalUnion H.canonicalOpenConnection) :=
  Classical.choice (P.a21 (intrinsicOpenMetric g H.canonicalOpenSet)
    (H.restrictToCanonicalUnion H.canonicalOpenConnection) hsmall)

end PoincareConjecture.ConnectedNeckCapCover
