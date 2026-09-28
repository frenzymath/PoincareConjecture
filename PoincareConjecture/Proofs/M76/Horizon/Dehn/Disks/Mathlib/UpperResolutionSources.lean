import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.NormalizedAttachmentSources








set_option autoImplicit false

open Set Metric Geometry TriangleDiskModel

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "I01" => Icc (0 : ℝ) 1
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)
local notation "T" => (TR ∪ TL : Set P2)


structure UpperResolutionSources
    {EA EC X : Type*}
    [NormedAddCommGroup EA] [NormedSpace ℝ EA]
    [NormedAddCommGroup EC] [NormedSpace ℝ EC]
    (SA : Set EA) (SC : Set EC) (Sstrip : Set P2)
    (pA : I01 → EA) (pC : I01 → EC) (pminus pplus : I01 → Sstrip)
    (fA : EA → X) (fS : P2 → X) (fC : EC → X) (g : V2 → X) where
  nA : SA ≃ₜ TR
  nS : Sstrip ≃ₜ TL
  m : T ≃ₜ TR
  nC : SC ≃ₜ TL
  H : D ≃ₜ T
  pl_nA : nA.IsFinitePL
  pl_nS : nS.IsFinitePL
  pl_m : m.IsFinitePL
  pl_nC : nC.IsFinitePL
  pl_H : H.IsFinitePL
  fiberAS : ∀ (x : SA) (y : Sstrip), (nA x : P2) = nS y ↔
    ∃! t : I01, (x : EA) = pA t ∧ y = pminus t
  fiberC : ∀ (x : T) (y : SC), (m x : P2) = nC y ↔
    ∃! t : I01, (x : P2) = nS (pplus t) ∧ (y : EC) = pC t
  keepA : ∀ x : SA, g (H.symm (rightDiskCopy m (rightDiskCopy nA x))) = fA x
  keepS : ∀ x : Sstrip, g (H.symm (rightDiskCopy m (leftDiskCopy nS x))) = fS x
  keepC : ∀ x : SC, g (H.symm (leftDiskCopy nC x)) = fC x

namespace UpperResolutionSources

variable {EA EC X : Type*}
  [NormedAddCommGroup EA] [NormedSpace ℝ EA]
  [NormedAddCommGroup EC] [NormedSpace ℝ EC]
  {SA : Set EA} {SC : Set EC} {Sstrip : Set P2}
  {pA : I01 → EA} {pC : I01 → EC} {pminus pplus : I01 → Sstrip}
  {fA : EA → X} {fS : P2 → X} {fC : EC → X} {g : V2 → X}
  (s : UpperResolutionSources SA SC Sstrip pA pC pminus pplus fA fS fC g)

def jA (x : SA) : V2 := s.H.symm (rightDiskCopy s.m (rightDiskCopy s.nA x))

def jS (x : Sstrip) : V2 := s.H.symm (rightDiskCopy s.m (leftDiskCopy s.nS x))

def jC (x : SC) : V2 := s.H.symm (leftDiskCopy s.nC x)

theorem embeddings : Topology.IsEmbedding s.jA ∧ Topology.IsEmbedding s.jS ∧
    Topology.IsEmbedding s.jC := by
  have h := Topology.IsEmbedding.subtypeVal.comp s.H.symm.isEmbedding
  exact ⟨(h.comp (rightDiskCopy_isEmbedding s.m)).comp (rightDiskCopy_isEmbedding s.nA),
    (h.comp (rightDiskCopy_isEmbedding s.m)).comp (leftDiskCopy_isEmbedding s.nS),
    h.comp (leftDiskCopy_isEmbedding s.nC)⟩


theorem cover : (range s.jA ∪ range s.jS) ∪ range s.jC = D := by
  ext y
  constructor
  · rintro ((⟨x, rfl⟩ | ⟨x, rfl⟩) | ⟨x, rfl⟩) <;> exact (s.H.symm _).property
  · intro hy
    rcases diskCopies_cover s.m s.nC (s.H ⟨y, hy⟩) with ⟨z, hz⟩ | ⟨x, hx⟩
    · rcases diskCopies_cover s.nA s.nS z with ⟨x, rfl⟩ | ⟨x, rfl⟩
      · exact Or.inl (Or.inl ⟨x, by
          simpa only [jA, Homeomorph.symm_apply_apply] using
            congrArg (fun z : T ↦ (s.H.symm z : V2)) hz⟩)
      · exact Or.inl (Or.inr ⟨x, by
          simpa only [jS, Homeomorph.symm_apply_apply] using
            congrArg (fun z : T ↦ (s.H.symm z : V2)) hz⟩)
    · exact Or.inr ⟨x, by
        simpa only [jC, Homeomorph.symm_apply_apply] using
          congrArg (fun z : T ↦ (s.H.symm z : V2)) hx⟩


theorem preimage (U : Set X) : D ∩ g ⁻¹' U =
    (s.jA '' {x : SA | fA x ∈ U} ∪ s.jS '' {x : Sstrip | fS x ∈ U}) ∪
      s.jC '' {x : SC | fC x ∈ U} := by
  ext y
  constructor
  · rintro ⟨hy, hU⟩
    rcases s.cover.symm.subset hy with ((⟨x, rfl⟩ | ⟨x, rfl⟩) | ⟨x, rfl⟩)
    · exact Or.inl (Or.inl ⟨x, by
        simpa only [mem_preimage, mem_ofPred_eq, jA, s.keepA] using hU, rfl⟩)
    · exact Or.inl (Or.inr ⟨x, by
        simpa only [mem_preimage, mem_ofPred_eq, jS, s.keepS] using hU, rfl⟩)
    · exact Or.inr ⟨x, by
        simpa only [mem_preimage, mem_ofPred_eq, jC, s.keepC] using hU, rfl⟩
  · rintro ((⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩)
    · exact ⟨(s.H.symm _).property, by
        simpa only [mem_preimage, mem_ofPred_eq, jA, s.keepA] using hx⟩
    · exact ⟨(s.H.symm _).property, by
        simpa only [mem_preimage, mem_ofPred_eq, jS, s.keepS] using hx⟩
    · exact ⟨(s.H.symm _).property, by
        simpa only [mem_preimage, mem_ofPred_eq, jC, s.keepC] using hx⟩

end UpperResolutionSources

end PoincareConjecture.M76.Dehn
