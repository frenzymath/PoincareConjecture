import PoincareConjecture.Definitions.Ch09.NeckCapTopology










set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M]

structure CorrectedA19Conclusion (g : RiemannianMetric 3 M)
    (H : NeckOnlyCover g) where
  tube : EpsilonTubeCertificate g H.X
  epsilon_eq : tube.epsilon = H.epsilon
  source_subset : tube.chain.source_necks ⊆ H.necks
  selected_centers_mem : ∀ i ∈ tube.chain.shape.active,
    (tube.chain.neck i).center ∈ H.X
  contains_X : H.X ⊆ tube.carrier
  separating_necks : ∀ N ∈ H.necks, N.IsSeparating









inductive CorrectedA20Conclusion (g : RiemannianMetric 3 M)
    (H : NeckOnlyCover g)
  | tube (certificate : EpsilonTubeCertificate g H.X)
      (source_subset : certificate.chain.source_necks ⊆ H.necks)
      (selected_centers_mem : ∀ i ∈ certificate.chain.shape.active,
        (certificate.chain.neck i).center ∈ H.X)
      (epsilon_eq : certificate.epsilon = H.epsilon)
      (carrier_eq_univ : certificate.carrier = Set.univ)
      (separating_necks : ∀ N ∈ H.necks, N.IsSeparating)
  | fibration (certificate : SphereBundleCircleCertificate g H.X)
      (carrier_eq_univ : certificate.carrier = Set.univ)
      (epsilon_eq : certificate.epsilon = H.epsilon)
      (nonseparating_necks : ∀ N ∈ H.necks, N.IsNonseparating)

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

def AppendixA21Theory (g : RiemannianMetric 3 M)
    (H : ConnectedNeckCapCover g) : Prop :=
  Nonempty {R : NeckCapRegion g H.X // NeckCapRegionCompatible g H R}

def AppendixA19Theory (g : RiemannianMetric 3 M)
    (H : NeckOnlyCover g)
    (_hsep : ∀ N ∈ H.necks, N.IsSeparating) : Prop :=
  Nonempty (CorrectedA19Conclusion g H)

def AppendixA20Theory (g : RiemannianMetric 3 M)
    (H : NeckOnlyCover g) (_hwhole : H.X = Set.univ) : Prop :=
  Nonempty (CorrectedA20Conclusion g H)

def AppendixA25Theory (g : RiemannianMetric 3 M)
    (H : ConnectedNeckCapCover g) (_hwhole : H.isWhole) : Prop :=
  Nonempty (GlobalNeckCapConclusion g H.epsilon H.cap_constant)

structure NeckCapTopologyTheory (g : RiemannianMetric 3 M) where
  epsilon₀ : ℝ
  epsilon₀_pos : 0 < epsilon₀
  epsilon₀_le_one_two_hundred : epsilon₀ ≤ 1 / 200
  a19 : ∀ (H : NeckOnlyCover g), H.epsilon ≤ epsilon₀ →
    ∀ hsep, AppendixA19Theory g H hsep
  a20 : ∀ (H : NeckOnlyCover g), H.epsilon ≤ epsilon₀ →
    ∀ hwhole : H.X = Set.univ, AppendixA20Theory g H hwhole
  a21 : ∀ (H : ConnectedNeckCapCover g), H.epsilon ≤ epsilon₀ →
    AppendixA21Theory g H
  a25 : ∀ (H : ConnectedNeckCapCover g), H.epsilon ≤ epsilon₀ →
    ∀ hwhole, AppendixA25Theory g H hwhole




structure UniversalNeckCapTopologyTheory where
  epsilon₀ : ℝ
  epsilon₀_pos : 0 < epsilon₀
  epsilon₀_le_one_two_hundred : epsilon₀ ≤ 1 / 200
  local_theory : ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M],
    ∀ g : RiemannianMetric 3 M,
      ∃ H : NeckCapTopologyTheory g, H.epsilon₀ = epsilon₀

end PoincareConjecture
