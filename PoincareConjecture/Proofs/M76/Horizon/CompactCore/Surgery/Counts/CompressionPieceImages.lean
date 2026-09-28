import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.CompressionCapParametrization
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CubePrismBoundary
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductTriangulation
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLImageTriangulation
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "J" => Icc (-(1 / 2 : ℝ)) (1 / 2)

theorem exists_finite_compression_piece_images
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {L : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e L j) (phi : X → E)
    (hphiPL : ∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target) :
    ∃ (Block Annulus : SimplicialComplex ℝ E)
      (Caps Rims : Bool → SimplicialComplex ℝ E),
      Block.faces.Finite ∧ Block.space = phi '' P.closedStrip ∧
      Annulus.faces.Finite ∧ Annulus.space = phi '' (P.map '' (Q ×ˢ J)) ∧
      (∀ b, (Caps b).faces.Finite ∧ (Caps b).space = phi '' P.capDisk b) ∧
      ∀ b, (Rims b).faces.Finite ∧ (Rims b).space = phi '' P.capRimSet b := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_cubePrism (by norm_num : -(1 / 2 : ℝ) < 1 / 2)
  have hKfull : K.space ⊆ D ×ˢ Icc (-1 : ℝ) 1 := by
    rw [hKs]
    intro z hz
    exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  obtain ⟨Block, hBlock, hBlocks⟩ :=
    ((P.polyhedral.restrict_finite K hK hKfull).finitePiecewiseAffineOn_comp
      K hK hphiPL).exists_finite_triangulation_image
  have hBlockeq : Block.space = phi '' P.closedStrip := by
    rw [hBlocks, hKs, closedStrip, image_image]
    rfl
  obtain ⟨Square, hSquare, hSquares⟩ := exists_finite_unitCubeSphere (ι := Fin 2)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨Interval, hInterval, hIntervals, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (by norm_num : -(1 / 2 : ℝ) < 1 / 2)
  obtain ⟨Cylinder, hCylinder, hCylinders, _⟩ :=
    Square.exists_finite_triangulation_prod Interval hSquare hInterval
  have hCylinderEq : Cylinder.space = Q ×ˢ J := by
    rw [hCylinders, hSquares, hIntervals]
  have hCylinderFull : Cylinder.space ⊆ D ×ˢ Icc (-1 : ℝ) 1 := by
    rw [hCylinderEq]
    intro z hz
    exact ⟨sphere_subset_closedBall hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  obtain ⟨Annulus, hAnnulus, hAnnuluss⟩ :=
    ((P.polyhedral.restrict_finite Cylinder hCylinder hCylinderFull).finitePiecewiseAffineOn_comp
      Cylinder hCylinder hphiPL).exists_finite_triangulation_image
  have hAnnulusEq : Annulus.space = phi '' (P.map '' (Q ×ˢ J)) := by
    rw [hAnnuluss, hCylinderEq, image_image]
    rfl
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨Disk, hDisk, hDisks, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_unit_cube (ι := Fin 2)
  have hCap (b : Bool) : ∃ Cap : SimplicialComplex ℝ E,
      Cap.faces.Finite ∧ Cap.space = phi '' P.capDisk b := by
    have hPL : PolyhedralPLInCharts e (P.capParameter b) Disk.space :=
      hDisks.symm ▸ P.polyhedral_capParameter b
    obtain ⟨Cap, hCap, hCaps⟩ :=
      (hPL.finitePiecewiseAffineOn_comp Disk hDisk hphiPL).exists_finite_triangulation_image
    refine ⟨Cap, hCap, ?_⟩
    rw [hCaps, hDisks, ← P.capParameter_image_disk, image_image]
    rfl
  have hRim (b : Bool) : ∃ Rim : SimplicialComplex ℝ E,
      Rim.faces.Finite ∧ Rim.space = phi '' P.capRimSet b := by
    have hPL := (P.polyhedral_capParameter b).restrict_finite Square hSquare
      (hSquares.subset.trans sphere_subset_closedBall)
    obtain ⟨Rim, hRim, hRims⟩ :=
      (hPL.finitePiecewiseAffineOn_comp Square hSquare hphiPL).exists_finite_triangulation_image
    refine ⟨Rim, hRim, ?_⟩
    rw [hRims, hSquares, ← P.capParameter_image_rim, image_image]
    rfl
  choose Caps hCaps hCapsEq using hCap
  choose Rims hRims hRimsEq using hRim
  exact ⟨Block, Annulus, Caps, Rims, hBlock, hBlockeq, hAnnulus, hAnnulusEq,
    fun b => ⟨hCaps b, hCapsEq b⟩, fun b => ⟨hRims b, hRimsEq b⟩⟩

end PoincareConjecture.M76.OriginalDiskProduct
