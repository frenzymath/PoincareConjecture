import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Chain.Geometry
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.NormalizedAttachmentSources



set_option autoImplicit false
open Set Geometry TriangleDiskModel

namespace PoincareConjecture.M76.Dehn.NonspanningChainGeometry

local notation "P2" => (ℝ × ℝ)
local notation "I01" => Icc (0 : ℝ) 1
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)
local notation "T" => (TR ∪ TL : Set P2)
local notation "Strip" => PolygonalCrossingResolution.source

variable {SA SM SC : Set P2} {pA pL pR pC : I01 → P2}
  (s : NonspanningChainGeometry SA SM SC pA pL pR pC)

def copyA (x : SA) : T := rightDiskCopy s.mR
  (rightDiskCopy s.nAML (rightDiskCopy s.mL (rightDiskCopy s.nA x)))

def copyL (x : Strip) : T := rightDiskCopy s.mR
  (rightDiskCopy s.nAML (rightDiskCopy s.mL (leftDiskCopy s.nL x)))

def copyM (x : SM) : T := rightDiskCopy s.mR
  (rightDiskCopy s.nAML (leftDiskCopy s.nM x))

def copyR (x : Strip) : T := rightDiskCopy s.mR (leftDiskCopy s.nR x)

def copyC (x : SC) : T := leftDiskCopy s.nC x

theorem embeddings : Topology.IsEmbedding s.copyA ∧ Topology.IsEmbedding s.copyL ∧
    Topology.IsEmbedding s.copyM ∧ Topology.IsEmbedding s.copyR ∧
      Topology.IsEmbedding s.copyC := by
  exact ⟨(((rightDiskCopy_isEmbedding s.mR).comp
      (rightDiskCopy_isEmbedding s.nAML)).comp (rightDiskCopy_isEmbedding s.mL)).comp
      (rightDiskCopy_isEmbedding s.nA),
    (((rightDiskCopy_isEmbedding s.mR).comp
      (rightDiskCopy_isEmbedding s.nAML)).comp (rightDiskCopy_isEmbedding s.mL)).comp
      (leftDiskCopy_isEmbedding s.nL),
    ((rightDiskCopy_isEmbedding s.mR).comp (rightDiskCopy_isEmbedding s.nAML)).comp
      (leftDiskCopy_isEmbedding s.nM),
    (rightDiskCopy_isEmbedding s.mR).comp (leftDiskCopy_isEmbedding s.nR),
    leftDiskCopy_isEmbedding s.nC⟩

theorem cover : (((range s.copyA ∪ range s.copyL) ∪ range s.copyM) ∪
    range s.copyR) ∪ range s.copyC = univ := by
  apply eq_univ_of_forall
  intro z
  rcases diskCopies_cover s.mR s.nC z with ⟨z3, rfl⟩ | ⟨x, rfl⟩
  · rcases diskCopies_cover s.nAML s.nR z3 with ⟨z2, rfl⟩ | ⟨x, rfl⟩
    · rcases diskCopies_cover s.mL s.nM z2 with ⟨z1, rfl⟩ | ⟨x, rfl⟩
      · rcases diskCopies_cover s.nA s.nL z1 with ⟨x, rfl⟩ | ⟨x, rfl⟩
        · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨x, rfl⟩)))
        · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨x, rfl⟩)))
      · exact Or.inl (Or.inl (Or.inr ⟨x, rfl⟩))
    · exact Or.inl (Or.inr ⟨x, rfl⟩)
  · exact Or.inr ⟨x, rfl⟩

private theorem comp_representative {S U V : Set P2} (j : S → U)
    (hj : ∃ f : P2 → P2, FinitePiecewiseAffineOn f S ∧ ∀ x : S, (j x : P2) = f x)
    (n : U ≃ₜ V) (hn : n.IsFinitePL) :
    ∃ f : P2 → P2, FinitePiecewiseAffineOn f S ∧ ∀ x : S, (n (j x) : P2) = f x := by
  obtain ⟨f, hf, hfv⟩ := hj
  obtain ⟨g, hg, hgv⟩ := hn
  have hm : MapsTo f S U := by
    intro x hx
    rw [← hfv ⟨x, hx⟩]
    exact (j ⟨x, hx⟩).property
  refine ⟨g ∘ f, hg.comp hf hm, ?_⟩
  intro x
  rw [hgv, hfv]
  rfl

theorem copyA_representative : ∃ f : P2 → P2, FinitePiecewiseAffineOn f SA ∧
    ∀ x : SA, (s.copyA x : P2) = f x := by
  have h1 := comp_representative (rightDiskCopy s.nA) s.pl_nA s.mL s.pl_mL
  have h2 := comp_representative (rightDiskCopy s.mL ∘ rightDiskCopy s.nA)
    h1 s.nAML s.pl_nAML
  exact comp_representative
    (rightDiskCopy s.nAML ∘ rightDiskCopy s.mL ∘ rightDiskCopy s.nA) h2 s.mR s.pl_mR

theorem copyL_representative : ∃ f : P2 → P2, FinitePiecewiseAffineOn f Strip ∧
    ∀ x : Strip, (s.copyL x : P2) = f x := by
  have h1 := comp_representative (leftDiskCopy s.nL) s.pl_nL s.mL s.pl_mL
  have h2 := comp_representative (rightDiskCopy s.mL ∘ leftDiskCopy s.nL)
    h1 s.nAML s.pl_nAML
  exact comp_representative
    (rightDiskCopy s.nAML ∘ rightDiskCopy s.mL ∘ leftDiskCopy s.nL) h2 s.mR s.pl_mR

theorem copyM_representative : ∃ f : P2 → P2, FinitePiecewiseAffineOn f SM ∧
    ∀ x : SM, (s.copyM x : P2) = f x := by
  have h1 := comp_representative (leftDiskCopy s.nM) s.pl_nM s.nAML s.pl_nAML
  exact comp_representative (rightDiskCopy s.nAML ∘ leftDiskCopy s.nM)
    h1 s.mR s.pl_mR

theorem copyR_representative : ∃ f : P2 → P2, FinitePiecewiseAffineOn f Strip ∧
    ∀ x : Strip, (s.copyR x : P2) = f x :=
  comp_representative (leftDiskCopy s.nR) s.pl_nR s.mR s.pl_mR

theorem copyC_representative : ∃ f : P2 → P2, FinitePiecewiseAffineOn f SC ∧
    ∀ x : SC, (s.copyC x : P2) = f x := s.pl_nC

end PoincareConjecture.M76.Dehn.NonspanningChainGeometry
