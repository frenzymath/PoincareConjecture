import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.Counts.CompressionPieceImages
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedraSubcomplexes

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "J" => Icc (-(1 / 2 : ℝ)) (1 / 2)

theorem exists_marked_compression_images
    {E Eold X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup Eold] [NormedSpace ℝ Eold]
    [FiniteDimensional ℝ Eold] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {L F : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e L j) (phi : X → E)
    (hphiPL : ∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hFK : phi '' F ⊆ K.space) (hBK : phi '' P.closedStrip ⊆ K.space)
    {n : ℕ} (Old : Fin n → SimplicialComplex ℝ Eold) (g : Eold → X)
    (hOld : ∀ i, (Old i).faces.Finite)
    (hg : ∀ i, PolyhedralPLInCharts e g (Old i).space)
    (hF : (⋃ i, g '' (Old i).space) = F) :
    ∃ (R A Block Annulus : SimplicialComplex ℝ E)
      (Caps Rims : Bool → SimplicialComplex ℝ E),
      R.faces.Finite ∧ R.IsSubdivision K ∧
      A ≤ R ∧ A.space = phi '' F ∧
      Block ≤ R ∧ Block.space = phi '' P.closedStrip ∧
      Annulus ≤ R ∧ Annulus.space = phi '' (P.map '' (Q ×ˢ J)) ∧
      (∀ b, Caps b ≤ R ∧ (Caps b).space = phi '' P.capDisk b) ∧
      ∀ b, Rims b ≤ R ∧ (Rims b).space = phi '' P.capRimSet b := by
  classical
  have hOldImage (i : Fin n) : ∃ T : SimplicialComplex ℝ E,
      T.faces.Finite ∧ T.space = phi '' (g '' (Old i).space) := by
    obtain ⟨T, hT, hTs⟩ :=
      ((hg i).finitePiecewiseAffineOn_comp (Old i) (hOld i) hphiPL).exists_finite_triangulation_image
    refine ⟨T, hT, ?_⟩
    rw [hTs, image_image]
    rfl
  choose OldImage hOldImage hOldImageEq using hOldImage
  obtain ⟨OldUnion, hOldUnion, hOldUnionEq, _⟩ :=
    SimplicialComplex.exists_finite_triangulation_iUnion OldImage hOldImage
  have hOldUnionF : OldUnion.space = phi '' F := by
    rw [hOldUnionEq, ← hF, image_iUnion]
    exact congrArg (fun A : Fin n → Set E => ⋃ i, A i) (funext hOldImageEq)
  obtain ⟨Block, Annulus, Caps, Rims, hBlock, hBlocks, hAnn, hAnns, hCaps, hRims⟩ :=
    P.exists_finite_compression_piece_images phi hphiPL
  have hAnnBlock : Annulus.space ⊆ phi '' P.closedStrip := by
    rw [hAnns]
    exact image_mono (image_mono (prod_mono sphere_subset_closedBall subset_rfl))
  have hCapBlock (b : Bool) : (Caps b).space ⊆ phi '' P.closedStrip := by
    rw [(hCaps b).2]
    apply image_mono
    rintro y ⟨z, hz, rfl⟩
    refine ⟨z, ⟨hz.1, ?_⟩, rfl⟩
    have ht : z.2 = if b then (1 / 2 : ℝ) else -(1 / 2) := hz.2
    rw [ht]
    cases b <;> norm_num
  have hRimBlock (b : Bool) : (Rims b).space ⊆ phi '' P.closedStrip := by
    rw [(hRims b).2]
    exact (image_mono (P.capRimSet_subset_capDisk b)).trans
      ((hCaps b).2 ▸ hCapBlock b)
  let pieces : Fin 7 → SimplicialComplex ℝ E :=
    ![OldUnion, Block, Annulus, Caps false, Caps true, Rims false, Rims true]
  have hpieces (i : Fin 7) : (pieces i).faces.Finite := by
    fin_cases i <;> dsimp [pieces] <;>
      first | assumption | exact (hCaps _).1 | exact (hRims _).1
  have hpiecesK (i : Fin 7) : (pieces i).space ⊆ K.space := by
    fin_cases i
    · exact hOldUnionF.subset.trans hFK
    · exact hBlocks.subset.trans hBK
    · exact hAnnBlock.trans hBK
    · exact (hCapBlock false).trans hBK
    · exact (hCapBlock true).trans hBK
    · exact (hRimBlock false).trans hBK
    · exact (hRimBlock true).trans hBK
  obtain ⟨R, marks, hR, hRK, hmarks⟩ :=
    K.exists_subdivision_with_finite_polyhedra hK pieces hpieces hpiecesK
  refine ⟨R, marks 0, marks 1, marks 2,
    (fun b => if b then marks 4 else marks 3),
    (fun b => if b then marks 6 else marks 5), hR, hRK,
    (hmarks 0).1, (hmarks 0).2.trans hOldUnionF,
    (hmarks 1).1, (hmarks 1).2.trans hBlocks,
    (hmarks 2).1, (hmarks 2).2.trans hAnns, ?_, ?_⟩
  · intro b
    cases b
    · exact ⟨(hmarks 3).1, (hmarks 3).2.trans (hCaps false).2⟩
    · exact ⟨(hmarks 4).1, (hmarks 4).2.trans (hCaps true).2⟩
  · intro b
    cases b
    · exact ⟨(hmarks 5).1, (hmarks 5).2.trans (hRims false).2⟩
    · exact ⟨(hmarks 6).1, (hmarks 6).2.trans (hRims true).2⟩

end PoincareConjecture.M76.OriginalDiskProduct
