import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.Tube.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.Tube.Chain
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.Cap.Topology
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Regions
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cylinder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M27TwistedSphereLineFlowCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}

def positiveEndTubeOfChain (C : M27TwistedSphereLineFlowCertificate K)
    {g : RiemannianMetric 3 M} {epsilon r : ℝ} (hr : 0 ≤ r)
    (hε : 0 < epsilon) (hsmall : epsilon ≤ 1 / 200)
    (chain : BalancedNeckChain g epsilon)
    (hunion : (⋃ i : {i // i ∈ chain.shape.active}, (chain.neck i.1).carrier) =
      (C.slabCore r)ᶜ)
    (hspheres : ∀ i ∈ chain.shape.active, ∃ h : ℝ, r < h ∧
      (chain.neck i).central_sphere = range (fun q => C.cover (q, h))) :
    EpsilonTubeCertificate g ∅ where
  epsilon := epsilon
  epsilon_pos := hε
  epsilon_le_threshold := hsmall
  carrier := (C.slabCore r)ᶜ
  carrier_open := (C.isCompact_slabCore r).isClosed.isOpen_compl
  contains_X := empty_subset _
  chain := chain
  carrier_eq_chain_union := hunion.symm
  cylinder := C.positiveEndCylinder hr
  central_sphere_isotopy := by
    intro i hi
    obtain ⟨h, hh, hS⟩ := hspheres i hi
    rw [hS]
    exact C.positiveEndSlice_isotopic_middleSphere hr hh

theorem capCarrier_inter_positiveEnd (C : M27TwistedSphereLineFlowCertificate K)
    {L : ℝ} (hL : 0 < L) :
    interior (C.slabCore (3 * L)) ∩ (C.slabCore L)ᶜ =
      C.cover '' (univ ×ˢ Ioo L (3 * L)) := by
  ext x
  obtain ⟨p, rfl⟩ := C.cover_surjective x
  rw [mem_inter_iff, mem_compl_iff, C.cover_mem_interior_slabCore_iff,
    C.cover_mem_slabCore_iff, C.cover_mem_positiveSlab_iff hL.le, not_le]
  exact and_comm

theorem capCarrier_union_positiveEnd (C : M27TwistedSphereLineFlowCertificate K)
    {L : ℝ} (hL : 0 < L) :
    interior (C.slabCore (3 * L)) ∪ (C.slabCore L)ᶜ = univ := by
  apply eq_univ_of_forall
  intro x
  by_cases hx : x ∈ C.slabCore L
  · exact Or.inl (C.slabCore_subset_capCarrier hL hx)
  · exact Or.inr hx

theorem positiveEndCylinder_cap_tail (C : M27TwistedSphereLineFlowCertificate K)
    {L : ℝ} (hL : 0 < L) :
    ∃ a ∈ Ioo (0 : ℝ) 1, (C.positiveEndCylinder hL.le).tail false a ⊆
      interior (C.slabCore (3 * L)) := by
  let a : ℝ := L / (1 + L)
  have hden : 0 < 1 + L := by linarith
  have ha : a ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos hL hden, (div_lt_one hden).mpr (by linarith)⟩
  have hratio : a / (1 - a) = L := by
    dsimp only [a]
    field_simp
    ring
  refine ⟨a, ha, ?_⟩
  rw [C.positiveEndCylinder_tail_false hL.le ha, hratio]
  intro x hx
  obtain ⟨p, rfl⟩ := C.cover_surjective x
  rw [C.cover_mem_interior_slabCore_iff]
  have hp := ((C.cover_mem_positiveSlab_iff hL.le p).mp hx).2
  linarith

section Attachment

variable (C : M27TwistedSphereLineFlowCertificate K)
  {g : RiemannianMetric 3 M} {epsilon L : ℝ} (hL : 0 < L)
  (hε : 0 < epsilon) (hsmall : epsilon ≤ 1 / 200)
  (chain : BalancedNeckChain g epsilon)
  (hunion : (⋃ i : {i // i ∈ chain.shape.active}, (chain.neck i.1).carrier) =
    (C.slabCore L)ᶜ)
  (hspheres : ∀ i ∈ chain.shape.active, ∃ h : ℝ, L < h ∧
    (chain.neck i).central_sphere = range (fun q => C.cover (q, h)))
  (cap : CapCertificate g)
  (hcap : cap.carrier = interior (C.slabCore (3 * L)))
  (hend : cap.end_neck.carrier = C.cover '' (univ ×ˢ Ioo L (3 * L)))

def positiveEndCapAttachment :
    CapTubeAttachment cap
      (C.positiveEndTubeOfChain hL.le hε hsmall chain hunion hspheres) false where
  overlap_model := by
    change OpenCylinderModel (cap.carrier ∩ (C.slabCore L)ᶜ)
    rw [hcap, C.capCarrier_inter_positiveEnd hL, ← hend]
    exact cap.end_neck.openCylinderModel
  tube_tail := by
    change ∃ a ∈ Ioo (0 : ℝ) 1, (C.positiveEndCylinder hL.le).tail false a ⊆ cap.carrier
    rw [hcap]
    exact C.positiveEndCylinder_cap_tail hL
  cap_tail := by
    have hinv : 0 < cap.epsilon⁻¹ := inv_pos.mpr cap.epsilon_pos
    refine ⟨cap.epsilon⁻¹ / 2, ⟨by linarith, by linarith⟩, ?_⟩
    intro x hx
    have hendx : x ∈ C.cover '' (univ ×ˢ Ioo L (3 * L)) := hend ▸ hx.1
    obtain ⟨p, rfl⟩ := C.cover_surjective x
    change C.cover p ∉ C.slabCore L
    rw [C.cover_mem_slabCore_iff]
    exact not_le.mpr ((C.cover_mem_positiveSlab_iff hL.le p).mp hendx).1

def cappedTubeOfPositiveEndChain : CappedTubeCertificate g where
  carrier := univ
  cap := cap
  tube := C.positiveEndTubeOfChain hL.le hε hsmall chain hunion hspheres
  cap_subset := subset_univ _
  tube_subset := subset_univ _
  carrier_eq_union := by
    change univ = cap.carrier ∪ (C.slabCore L)ᶜ
    rw [hcap, C.capCarrier_union_positiveEnd hL]
  connected := isConnected_univ
  attachment_side := false
  attachment := C.positiveEndCapAttachment hL hε hsmall chain hunion hspheres cap hcap hend

end Attachment

section ExplicitChain

variable (C : M27TwistedSphereLineFlowCertificate K)
  {t epsilon : ℝ} (ht : t ≤ 0) (hε : 0 < epsilon) (hsmall : epsilon ≤ 1 / 200)
  (q : UnitTwoSphere)
  (a : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere)
  (ha : ∀ (x : UnitTwoSphere) (v w : TangentSpace (𝓡 2) x),
    (K.flow.connection t).scalarCurvature (C.cover (q, 0)) *
      (C.sphere.metric t).inner (a x)
        (mfderiv (𝓡 2) (𝓡 2) a x v) (mfderiv (𝓡 2) (𝓡 2) a x w) =
          2 * (Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2).inner x v w)

private theorem balancedEndChain_slices :
    ∀ i ∈ (C.balancedEndChain ht hε (by linarith) q a ha).shape.active,
      ∃ h : ℝ, C.neckSpacing (t := t) (epsilon := epsilon) q < h ∧
        ((C.balancedEndChain ht hε (by linarith) q a ha).neck i).central_sphere =
          range (fun z => C.cover (z, h)) := by
  intro i hi
  change 0 ≤ i at hi
  refine ⟨((i : ℝ) + 2) * C.neckSpacing (t := t) (epsilon := epsilon) q, ?_, ?_⟩
  · have hi' : (0 : ℝ) ≤ i := by exact_mod_cast hi
    have hL := C.neckSpacing_pos ht hε q
    nlinarith
  · change (C.endNeck ht hε (by linarith) q a ha i).terminal_neck.central_sphere = _
    rw [C.endNeck_central_sphere ht hε (by linarith) q a ha i hi]
    ext x
    constructor
    · rintro ⟨⟨z, s⟩, ⟨_, hs⟩, he⟩
      have hs' : s = ((i : ℝ) + 2) * C.neckSpacing (t := t) (epsilon := epsilon) q := hs
      subst s
      exact ⟨z, he⟩
    · rintro ⟨z, rfl⟩
      exact ⟨(z, _), ⟨mem_univ _, rfl⟩, rfl⟩

def positiveEndTube : EpsilonTubeCertificate (K.flow.metric t) ∅ :=
  C.positiveEndTubeOfChain (C.neckSpacing_pos ht hε q).le hε hsmall
    (C.balancedEndChain ht hε (by linarith) q a ha)
    (C.balancedEndChain_union ht hε (by linarith) q a ha)
    (C.balancedEndChain_slices ht hε hsmall q a ha)

@[simp] theorem positiveEndTube_epsilon :
    (C.positiveEndTube ht hε hsmall q a ha).epsilon = epsilon := rfl

@[simp] theorem positiveEndTube_carrier :
    (C.positiveEndTube ht hε hsmall q a ha).carrier =
      (C.slabCore (C.neckSpacing (t := t) (epsilon := epsilon) q))ᶜ := rfl

variable (cap : CapCertificate (K.flow.metric t))
  (hcarrier : cap.carrier =
    interior (C.slabCore (3 * C.neckSpacing (t := t) (epsilon := epsilon) q)))
  (hend : cap.end_neck.carrier = C.cover '' (univ ×ˢ Ioo
    (C.neckSpacing (t := t) (epsilon := epsilon) q)
    (3 * C.neckSpacing (t := t) (epsilon := epsilon) q)))

def cappedTubeOfSlabCap : CappedTubeCertificate (K.flow.metric t) :=
  C.cappedTubeOfPositiveEndChain (C.neckSpacing_pos ht hε q) hε hsmall
    (C.balancedEndChain ht hε (by linarith) q a ha)
    (C.balancedEndChain_union ht hε (by linarith) q a ha)
    (C.balancedEndChain_slices ht hε hsmall q a ha) cap hcarrier hend

@[simp] theorem cappedTubeOfSlabCap_cap :
    (C.cappedTubeOfSlabCap ht hε hsmall q a ha cap hcarrier hend).cap = cap := rfl

@[simp] theorem cappedTubeOfSlabCap_tube :
    (C.cappedTubeOfSlabCap ht hε hsmall q a ha cap hcarrier hend).tube =
      C.positiveEndTube ht hε hsmall q a ha := rfl

@[simp] theorem cappedTubeOfSlabCap_carrier :
    (C.cappedTubeOfSlabCap ht hε hsmall q a ha cap hcarrier hend).carrier = univ := rfl

@[simp] theorem cappedTubeOfSlabCap_tube_epsilon :
    (C.cappedTubeOfSlabCap ht hε hsmall q a ha cap hcarrier hend).tube.epsilon = epsilon := rfl

@[simp] theorem cappedTubeOfSlabCap_tube_carrier :
    (C.cappedTubeOfSlabCap ht hε hsmall q a ha cap hcarrier hend).tube.carrier =
      (C.slabCore (C.neckSpacing (t := t) (epsilon := epsilon) q))ᶜ := rfl

end ExplicitChain

end PoincareConjecture.M27TwistedSphereLineFlowCertificate
