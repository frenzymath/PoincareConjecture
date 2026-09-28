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

structure AlternateResolutionSources
    {EA EM EC X : Type*}
    [NormedAddCommGroup EA] [NormedSpace ℝ EA]
    [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [NormedAddCommGroup EC] [NormedSpace ℝ EC]
    (SA : Set EA) (SM : Set EM) (SC : Set EC) (Sstrip : Set P2)
    (pA : I01 → EA) (pL pR : I01 → EM) (pC : I01 → EC)
    (pminus pplus : I01 → Sstrip)
    (fA : EA → X) (fL : P2 → X) (fM : EM → X) (fR : P2 → X) (fC : EC → X)
    (g : V2 → X) where
  nA : SA ≃ₜ TR
  nL : Sstrip ≃ₜ TL
  mL : T ≃ₜ TR
  nM : SM ≃ₜ TL
  nAML : T ≃ₜ TR
  nR : Sstrip ≃ₜ TL
  mR : T ≃ₜ TR
  nC : SC ≃ₜ TL
  H : D ≃ₜ T
  pl_nA : nA.IsFinitePL
  pl_nL : nL.IsFinitePL
  pl_mL : mL.IsFinitePL
  pl_nM : nM.IsFinitePL
  pl_nAML : nAML.IsFinitePL
  pl_nR : nR.IsFinitePL
  pl_mR : mR.IsFinitePL
  pl_nC : nC.IsFinitePL
  pl_H : H.IsFinitePL
  pR_mem : ∀ t : I01, pR t ∈ SM
  fiberAL : ∀ (x : SA) (y : Sstrip), (nA x : P2) = nL y ↔
    ∃! t : I01, (x : EA) = pA t ∧ y = pplus t
  fiberM : ∀ (x : T) (y : SM), (mL x : P2) = nM y ↔
    ∃! t : I01, (x : P2) = nL (pminus t) ∧ (y : EM) = pL t
  fiberR : ∀ (x : T) (y : Sstrip), (nAML x : P2) = nR y ↔
    ∃! t : I01, (x : P2) = nM ⟨pR t, pR_mem t⟩ ∧ y = pminus t
  fiberC : ∀ (x : T) (y : SC), (mR x : P2) = nC y ↔
    ∃! t : I01, (x : P2) = nR (pplus t) ∧ (y : EC) = pC t
  keepA : ∀ x : SA, g (H.symm (rightDiskCopy mR
    (rightDiskCopy nAML (rightDiskCopy mL (rightDiskCopy nA x))))) = fA x
  keepL : ∀ x : Sstrip, g (H.symm (rightDiskCopy mR
    (rightDiskCopy nAML (rightDiskCopy mL (leftDiskCopy nL x))))) = fL x
  keepM : ∀ x : SM, g (H.symm (rightDiskCopy mR
    (rightDiskCopy nAML (leftDiskCopy nM x)))) = fM x
  keepR : ∀ x : Sstrip, g (H.symm (rightDiskCopy mR (leftDiskCopy nR x))) = fR x
  keepC : ∀ x : SC, g (H.symm (leftDiskCopy nC x)) = fC x

namespace AlternateResolutionSources

variable {EA EM EC X : Type*}
  [NormedAddCommGroup EA] [NormedSpace ℝ EA]
  [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  [NormedAddCommGroup EC] [NormedSpace ℝ EC]
  {SA : Set EA} {SM : Set EM} {SC : Set EC} {Sstrip : Set P2}
  {pA : I01 → EA} {pL pR : I01 → EM} {pC : I01 → EC}
  {pminus pplus : I01 → Sstrip}
  {fA : EA → X} {fL : P2 → X} {fM : EM → X} {fR : P2 → X} {fC : EC → X}
  {g : V2 → X}
  (s : AlternateResolutionSources SA SM SC Sstrip pA pL pR pC pminus pplus
    fA fL fM fR fC g)

def jA (x : SA) : V2 := s.H.symm (rightDiskCopy s.mR
  (rightDiskCopy s.nAML (rightDiskCopy s.mL (rightDiskCopy s.nA x))))

def jL (x : Sstrip) : V2 := s.H.symm (rightDiskCopy s.mR
  (rightDiskCopy s.nAML (rightDiskCopy s.mL (leftDiskCopy s.nL x))))

def jM (x : SM) : V2 := s.H.symm (rightDiskCopy s.mR
  (rightDiskCopy s.nAML (leftDiskCopy s.nM x)))

def jR (x : Sstrip) : V2 := s.H.symm (rightDiskCopy s.mR (leftDiskCopy s.nR x))

def jC (x : SC) : V2 := s.H.symm (leftDiskCopy s.nC x)

theorem embeddings : Topology.IsEmbedding s.jA ∧ Topology.IsEmbedding s.jL ∧
    Topology.IsEmbedding s.jM ∧ Topology.IsEmbedding s.jR ∧ Topology.IsEmbedding s.jC := by
  have h := Topology.IsEmbedding.subtypeVal.comp s.H.symm.isEmbedding
  exact ⟨(((h.comp (rightDiskCopy_isEmbedding s.mR)).comp
    (rightDiskCopy_isEmbedding s.nAML)).comp (rightDiskCopy_isEmbedding s.mL)).comp
      (rightDiskCopy_isEmbedding s.nA),
    (((h.comp (rightDiskCopy_isEmbedding s.mR)).comp
    (rightDiskCopy_isEmbedding s.nAML)).comp (rightDiskCopy_isEmbedding s.mL)).comp
      (leftDiskCopy_isEmbedding s.nL),
    ((h.comp (rightDiskCopy_isEmbedding s.mR)).comp
      (rightDiskCopy_isEmbedding s.nAML)).comp (leftDiskCopy_isEmbedding s.nM),
    (h.comp (rightDiskCopy_isEmbedding s.mR)).comp (leftDiskCopy_isEmbedding s.nR),
    h.comp (leftDiskCopy_isEmbedding s.nC)⟩

theorem cover : (((range s.jA ∪ range s.jL) ∪ range s.jM) ∪ range s.jR) ∪
    range s.jC = D := by
  ext y
  constructor
  · rintro ((((⟨x, rfl⟩ | ⟨x, rfl⟩) | ⟨x, rfl⟩) | ⟨x, rfl⟩) | ⟨x, rfl⟩) <;>
      exact (s.H.symm _).property
  · intro hy
    rcases diskCopies_cover s.mR s.nC (s.H ⟨y, hy⟩) with ⟨z3, hz3⟩ | ⟨x, hx⟩
    · rcases diskCopies_cover s.nAML s.nR z3 with ⟨z2, rfl⟩ | ⟨x, rfl⟩
      · rcases diskCopies_cover s.mL s.nM z2 with ⟨z1, rfl⟩ | ⟨x, rfl⟩
        · rcases diskCopies_cover s.nA s.nL z1 with ⟨x, rfl⟩ | ⟨x, rfl⟩
          · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨x, by
              simpa only [jA, Homeomorph.symm_apply_apply] using
                congrArg (fun z : T ↦ (s.H.symm z : V2)) hz3⟩)))
          · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨x, by
              simpa only [jL, Homeomorph.symm_apply_apply] using
                congrArg (fun z : T ↦ (s.H.symm z : V2)) hz3⟩)))
        · exact Or.inl (Or.inl (Or.inr ⟨x, by
            simpa only [jM, Homeomorph.symm_apply_apply] using
              congrArg (fun z : T ↦ (s.H.symm z : V2)) hz3⟩))
      · exact Or.inl (Or.inr ⟨x, by
          simpa only [jR, Homeomorph.symm_apply_apply] using
            congrArg (fun z : T ↦ (s.H.symm z : V2)) hz3⟩)
    · exact Or.inr ⟨x, by
        simpa only [jC, Homeomorph.symm_apply_apply] using
          congrArg (fun z : T ↦ (s.H.symm z : V2)) hx⟩

theorem preimage (U : Set X) : D ∩ g ⁻¹' U =
    (((s.jA '' {x : SA | fA x ∈ U} ∪ s.jL '' {x : Sstrip | fL x ∈ U}) ∪
      s.jM '' {x : SM | fM x ∈ U}) ∪ s.jR '' {x : Sstrip | fR x ∈ U}) ∪
      s.jC '' {x : SC | fC x ∈ U} := by
  ext y
  constructor
  · rintro ⟨hy, hU⟩
    rcases s.cover.symm.subset hy with
      ((((⟨x, rfl⟩ | ⟨x, rfl⟩) | ⟨x, rfl⟩) | ⟨x, rfl⟩) | ⟨x, rfl⟩)
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨x, by
        simpa only [mem_preimage, mem_ofPred_eq, jA, s.keepA] using hU, rfl⟩)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨x, by
        simpa only [mem_preimage, mem_ofPred_eq, jL, s.keepL] using hU, rfl⟩)))
    · exact Or.inl (Or.inl (Or.inr ⟨x, by
        simpa only [mem_preimage, mem_ofPred_eq, jM, s.keepM] using hU, rfl⟩))
    · exact Or.inl (Or.inr ⟨x, by
        simpa only [mem_preimage, mem_ofPred_eq, jR, s.keepR] using hU, rfl⟩)
    · exact Or.inr ⟨x, by simpa only [mem_preimage, mem_ofPred_eq, jC, s.keepC] using hU, rfl⟩
  · rintro ((((⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩) |
      ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩)
    · exact ⟨(s.H.symm _).property, by simpa only [mem_preimage, mem_ofPred_eq, jA, s.keepA] using hx⟩
    · exact ⟨(s.H.symm _).property, by simpa only [mem_preimage, mem_ofPred_eq, jL, s.keepL] using hx⟩
    · exact ⟨(s.H.symm _).property, by simpa only [mem_preimage, mem_ofPred_eq, jM, s.keepM] using hx⟩
    · exact ⟨(s.H.symm _).property, by simpa only [mem_preimage, mem_ofPred_eq, jR, s.keepR] using hx⟩
    · exact ⟨(s.H.symm _).property, by simpa only [mem_preimage, mem_ofPred_eq, jC, s.keepC] using hx⟩

end AlternateResolutionSources

end PoincareConjecture.M76.Dehn
