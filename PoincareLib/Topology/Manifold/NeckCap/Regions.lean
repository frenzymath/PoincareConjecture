import PoincareLib.Topology.Manifold.NeckCap.Chain
import PoincareLib.Topology.Manifold.NeckCap.Cover

/-!
# Neck and cap regions

Adapted from Mapher, `PoincareMT/Definitions/Ch09/NeckCapTopology.lean` and
`PoincareMT/Statements/Ch09/NeckCapTopology.lean`, commit
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M]

structure CapTubeAttachment {g : RiemannianMetric 3 M} {X : Set M}
    (cap : CapCertificate g) (tube : EpsilonTubeCertificate g X) (side : Bool) where
  overlap_model : OpenCylinderModel (cap.carrier ∩ tube.carrier)
  tube_tail : ∃ a ∈ Set.Ioo (0 : ℝ) 1, tube.cylinder.tail side a ⊆ cap.carrier
  cap_tail : ∃ s ∈ Set.Ioo 0 cap.epsilon⁻¹,
    cap.end_neck.region s cap.epsilon⁻¹ ⊆ tube.carrier

structure CappedTubeCertificate (g : RiemannianMetric 3 M) where
  carrier : Set M
  cap : CapCertificate g
  tube : EpsilonTubeCertificate g ∅
  cap_subset : cap.carrier ⊆ carrier
  tube_subset : tube.carrier ⊆ carrier
  carrier_eq_union : carrier = cap.carrier ∪ tube.carrier
  connected : IsConnected carrier
  attachment_side : Bool
  attachment : CapTubeAttachment cap tube attachment_side

structure DoubleCappedTubeCertificate (g : RiemannianMetric 3 M) where
  carrier : Set M
  cap₁ : CapCertificate g
  cap₂ : CapCertificate g
  tube : EpsilonTubeCertificate g ∅
  cap₁_subset : cap₁.carrier ⊆ carrier
  cap₂_subset : cap₂.carrier ⊆ carrier
  tube_subset : tube.carrier ⊆ carrier
  carrier_eq_union : carrier = cap₁.carrier ∪ tube.carrier ∪ cap₂.carrier
  disjoint_cores : Disjoint cap₁.closed_core cap₂.closed_core
  connected : IsConnected carrier
  compact : IsCompact carrier
  first_attachment : CapTubeAttachment cap₁ tube false
  second_attachment : CapTubeAttachment cap₂ tube true

structure SphereBundleCircleCertificate
    (g : RiemannianMetric 3 M) (X : Set M) where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_le_one_two_hundred : epsilon ≤ 1 / 200
  carrier : Set M
  contains_X : X ⊆ carrier
  connected : IsConnected carrier
  compact : IsCompact carrier
  component : ∃ x : M, carrier = connectedComponent x
  model : SphereBundleCircleModel.{u}
  homeomorph :
    letI : TopologicalSpace model.carrier := model.carrier_topology
    carrier ≃ₜ model.carrier
  forward : M → model.carrier
  inverse : model.carrier → M
  forward_eq :
    letI : TopologicalSpace model.carrier := model.carrier_topology
    ∀ x : carrier, forward x.1 = homeomorph x
  inverse_eq :
    letI : TopologicalSpace model.carrier := model.carrier_topology
    ∀ y, inverse y = (homeomorph.symm y).1
  forward_smooth :
    letI : TopologicalSpace model.carrier := model.carrier_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) model.carrier := model.carrier_charted
    letI : IsManifold (𝓡 3) ∞ model.carrier := model.carrier_manifold
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ forward carrier
  inverse_smooth :
    letI : TopologicalSpace model.carrier := model.carrier_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) model.carrier := model.carrier_charted
    letI : IsManifold (𝓡 3) ∞ model.carrier := model.carrier_manifold
    ContMDiff (𝓡 3) (𝓡 3) ∞ inverse
  necks : Set (EpsilonNeck g)
  neck_epsilon : ∀ N ∈ necks, N.epsilon = epsilon
  neck_cover : carrier = ⋃ N : {N // N ∈ necks}, N.1.carrier
  fiber_isotopy : ∀ N ∈ necks, ∃ b : UnitCircle,
    SmoothSphereIsotopicIn carrier N.central_sphere
      {x | x ∈ carrier ∧ model.projection (forward x) = b}

inductive NeckCapRegion (g : RiemannianMetric 3 M) (X : Set M)
  | twoCaps {Y : Set M} (kind : ClosedComponentKind)
      (cap₁ cap₂ : CapCertificate g)
      (component : ClosedComponentCertificate kind Y)
      (union_eq : Y = cap₁.carrier ∪ cap₂.carrier)
      (contains_X : X ⊆ Y)
  | doubleCappedTube (certificate : DoubleCappedTubeCertificate g)
      (kind : ClosedComponentKind)
      (component : ClosedComponentCertificate kind certificate.carrier)
      (contains_X : X ⊆ certificate.carrier)
  | singleCap (cap : CapCertificate g) (contains_X : X ⊆ cap.carrier)
  | cappedTube (certificate : CappedTubeCertificate g)
      (contains_X : X ⊆ certificate.carrier)
  | tube (tube : EpsilonTubeCertificate g X)
  | fibration (fibration : SphereBundleCircleCertificate g X)

def NeckCapRegionCompatible (g : RiemannianMetric 3 M)
    (H : ConnectedNeckCapCover g) : NeckCapRegion g H.X → Prop
  | .twoCaps _kind cap₁ cap₂ _component _union_eq _contains_X =>
      cap₁.epsilon = H.epsilon ∧ cap₂.epsilon = H.epsilon ∧
        cap₁.cap_constant ≤ H.cap_constant ∧ cap₂.cap_constant ≤ H.cap_constant
  | .doubleCappedTube certificate _kind _component _contains_X =>
      certificate.cap₁.epsilon = H.epsilon ∧ certificate.cap₂.epsilon = H.epsilon ∧
        certificate.tube.epsilon = H.epsilon ∧
        certificate.cap₁.cap_constant ≤ H.cap_constant ∧
        certificate.cap₂.cap_constant ≤ H.cap_constant
  | .singleCap cap _contains_X =>
      cap.epsilon = H.epsilon ∧ cap.cap_constant ≤ H.cap_constant
  | .cappedTube certificate _contains_X =>
      certificate.cap.epsilon = H.epsilon ∧ certificate.tube.epsilon = H.epsilon ∧
        certificate.cap.cap_constant ≤ H.cap_constant ∧
        Nonempty (CapTubeAttachment certificate.cap certificate.tube
          certificate.attachment_side)
  | .tube tube =>
      tube.epsilon = H.epsilon
  | .fibration fibration =>
      fibration.epsilon = H.epsilon ∧ H.X ⊆ fibration.carrier

structure NoncompactGlobalCertificate (g : RiemannianMetric 3 M)
    (epsilon C : ℝ) where
  carrier : Set M
  shape :
    (∃ cap : CapCertificate g,
      cap.carrier = carrier ∧ cap.epsilon = epsilon ∧
        cap.cap_constant ≤ C ∧
        (cap.model_kind = CapModelKind.euclidean ∨
          cap.model_kind = CapModelKind.puncturedProjective)) ∨
    (∃ certificate : CappedTubeCertificate g,
      certificate.carrier = carrier ∧ certificate.cap.epsilon = epsilon ∧
      certificate.tube.epsilon = epsilon ∧ certificate.cap.cap_constant ≤ C ∧
        (certificate.cap.model_kind = CapModelKind.euclidean ∨
          certificate.cap.model_kind = CapModelKind.puncturedProjective))
  whole : Set.univ ⊆ carrier

inductive GlobalClosedShape (g : RiemannianMetric 3 M)
    (epsilon C : ℝ) (Y : Set M)
  | twoCaps (cap₁ cap₂ : CapCertificate g)
      (union_eq : Y = cap₁.carrier ∪ cap₂.carrier)
      (cap₁_epsilon : cap₁.epsilon = epsilon)
      (cap₂_epsilon : cap₂.epsilon = epsilon)
      (cap₁_constant : cap₁.cap_constant ≤ C)
      (cap₂_constant : cap₂.cap_constant ≤ C)
  | doubleCappedTube (certificate : DoubleCappedTubeCertificate g)
      (carrier_eq : certificate.carrier = Y)
      (cap₁_epsilon : certificate.cap₁.epsilon = epsilon)
      (cap₂_epsilon : certificate.cap₂.epsilon = epsilon)
      (tube_epsilon : certificate.tube.epsilon = epsilon)
      (cap₁_constant : certificate.cap₁.cap_constant ≤ C)
      (cap₂_constant : certificate.cap₂.cap_constant ≤ C)

inductive GlobalNeckCapConclusion (g : RiemannianMetric 3 M) (epsilon C : ℝ)
  | closed (Y : Set M) (kind : ClosedComponentKind)
      (component : ClosedComponentCertificate kind Y)
      (whole : Set.univ ⊆ Y)
      (shape : GlobalClosedShape g epsilon C Y)
  | noncompact (certificate : NoncompactGlobalCertificate g epsilon C)
  | tube (tube : EpsilonTubeCertificate g Set.univ)
      (epsilon_eq : tube.epsilon = epsilon)
      (carrier_eq_univ : tube.carrier = Set.univ)
  | fibration (fibration : SphereBundleCircleCertificate g (Set.univ : Set M))
      (epsilon_eq : fibration.epsilon = epsilon)
      (carrier_eq_univ : fibration.carrier = Set.univ)

end PoincareMT
