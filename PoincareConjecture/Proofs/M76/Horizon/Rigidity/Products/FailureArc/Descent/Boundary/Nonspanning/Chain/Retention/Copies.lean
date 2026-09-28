import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Chain.Maps.Normalization
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.RetainedModels
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.JoinedSourceContinuity

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.NonspanningChainAnnulus

local notation "P2" => (ℝ × ℝ)
local notation "I01" => Icc (0 : ℝ) 1
local notation "Ann" => squareAnnulus 8 1
local notation "Index" => (NonspanningRetainedPiece ⊕ Bool)

variable {SA SM SC D : Set P2} {pA pL pR pC : I01 → P2}
  {s : NonspanningChainGeometry SA SM SC pA pL pR pC}
  {H : NonspanningChainHole s D} (N : NonspanningChainAnnulus H)

def retainedSet (_N : NonspanningChainAnnulus H) : Set P2 :=
  ((SA \ interior D) ∪ (SM \ interior D)) ∪ (SC \ interior D)

def sourceCopy (i : Index) (x : H.sourceSet i) : P2 := N.copy i x

noncomputable def retainedCopy (hAM : Disjoint SA SM) (hAC : Disjoint SA SC)
    (hMC : Disjoint SM SC) : N.retainedSet → P2 :=
  joinSourceCopies
    (disjoint_union_left.mpr ⟨hAC.mono sdiff_subset sdiff_subset,
      hMC.mono sdiff_subset sdiff_subset⟩)
    (joinSourceCopies (hAM.mono sdiff_subset sdiff_subset)
      (N.sourceCopy (.inl .first)) (N.sourceCopy (.inl .middle)))
    (N.sourceCopy (.inl .last))

theorem sourceCopy_embedding (i : Index) : IsEmbedding (N.sourceCopy i) :=
  IsEmbedding.subtypeVal.comp (N.copy_embedding i)

theorem retained_images_disjoint {i j : NonspanningRetainedPiece} (hij : i ≠ j) :
    Disjoint (range (N.sourceCopy (.inl i))) (range (N.sourceCopy (.inl j))) := by
  apply disjoint_left.mpr
  rintro z ⟨x, rfl⟩ ⟨y, hy⟩
  have h := (N.copy_eq_iff _ _ _ _).mp (Subtype.ext hy.symm)
  exact s.retainedCopy_ne hij ⟨x, x.property.1⟩ ⟨y, y.property.1⟩ h

theorem retainedCopy_injective (hAM : Disjoint SA SM) (hAC : Disjoint SA SC)
    (hMC : Disjoint SM SC) : Function.Injective (N.retainedCopy hAM hAC hMC) := by
  apply joinSourceCopies_injective
  · exact joinSourceCopies_injective _ (N.sourceCopy_embedding _).injective
      (N.sourceCopy_embedding _).injective (N.retained_images_disjoint (by decide))
  · exact (N.sourceCopy_embedding _).injective
  · erw [joinSourceCopies_range]
    exact disjoint_union_left.mpr ⟨N.retained_images_disjoint (by decide),
      N.retained_images_disjoint (by decide)⟩

theorem retainedCopy_range (hAM : Disjoint SA SM) (hAC : Disjoint SA SC)
    (hMC : Disjoint SM SC) : range (N.retainedCopy hAM hAC hMC) =
    (range (N.sourceCopy (.inl .first)) ∪ range (N.sourceCopy (.inl .middle))) ∪
      range (N.sourceCopy (.inl .last)) := by
  unfold retainedCopy
  erw [joinSourceCopies_range, joinSourceCopies_range]
  rfl

theorem retainedCopy_cover (hAM : Disjoint SA SM) (hAC : Disjoint SA SC)
    (hMC : Disjoint SM SC) :
    range (N.retainedCopy hAM hAC hMC) ∪
      (range (N.sourceCopy (.inr false)) ∪ range (N.sourceCopy (.inr true))) = Ann := by
  rw [N.retainedCopy_range]
  ext z
  constructor
  · rintro (((⟨x, rfl⟩ | ⟨x, rfl⟩) | ⟨x, rfl⟩) | (⟨x, rfl⟩ | ⟨x, rfl⟩)) <;>
      exact (N.copy _ x).property
  · intro hz
    obtain ⟨i, x, hx⟩ := mem_iUnion.mp (N.copy_cover.symm.subset (mem_univ (⟨z, hz⟩ : Ann)))
    have hv : N.sourceCopy i x = z := congrArg Subtype.val hx
    cases i with
    | inl i =>
      cases i with
      | first => exact Or.inl (Or.inl (Or.inl ⟨x, hv⟩))
      | middle => exact Or.inl (Or.inl (Or.inr ⟨x, hv⟩))
      | last => exact Or.inl (Or.inr ⟨x, hv⟩)
    | inr b =>
      cases b with
      | false => exact Or.inr (Or.inl ⟨x, hv⟩)
      | true => exact Or.inr (Or.inr ⟨x, hv⟩)

theorem retainedCopy_values {X : Type*} {f g : P2 → X} {τ : (P2 × ℝ) → X}
    (hAM : Disjoint SA SM) (hAC : Disjoint SA SC) (hMC : Disjoint SM SC)
    (hkeep : ∀ i (x : H.sourceSet i), g (N.copy i x) = NonspanningChainHole.pieceMap f τ i x)
    (x : N.retainedSet) : g (N.retainedCopy hAM hAC hMC x) = f x :=
  joinSourceCopies_target _ (fun y => joinSourceCopies_target _
    (hkeep (.inl .first)) (hkeep (.inl .middle)) y) (hkeep (.inl .last)) x

theorem retainedCopy_PL
    (hAM : Disjoint SA SM) (hAC : Disjoint SA SC) (hMC : Disjoint SM SC)
    (hS : ∀ i, IsFinitePLBallPair P2 (s.retainedSet i) (frontier (s.retainedSet i)))
    (hD : IsFinitePLBallPair P2 D (frontier D)) :
    ∃ j : P2 → P2, FinitePiecewiseAffineOn j N.retainedSet ∧
      ∀ x : N.retainedSet, j x = N.retainedCopy hAM hAC hMC x := by
  have hrep (i : Index) : ∃ j : P2 → P2, FinitePiecewiseAffineOn j (H.sourceSet i) ∧
      ∀ x : H.sourceSet i, j x = N.sourceCopy i x := by
    obtain ⟨j, hj, hjv⟩ := N.copy_representative hS hD i
    exact ⟨j, hj, fun x => (hjv x).symm⟩
  exact joinSourceCopies_exists_finitePL_extension _ _ _
    (joinSourceCopies_exists_finitePL_extension _ _ _ (hrep (.inl .first))
      (hrep (.inl .middle))) (hrep (.inl .last))

end PoincareConjecture.M76.Dehn.NonspanningChainAnnulus
