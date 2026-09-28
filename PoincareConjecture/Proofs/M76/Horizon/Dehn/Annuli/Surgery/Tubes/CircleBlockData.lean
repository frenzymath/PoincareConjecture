import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.ComponentBranchModel
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.ComponentCircleBlocks



set_option autoImplicit false
open Set Metric Geometry Topology Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

variable {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X] {S : Set E}
  {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X}
  {old : SourceCircleDecomposition f S} {i : old.Index}



structure ComponentCircleBlockData (D : ComponentBranchModel (e := e) (R := R) old i)
    [Fintype D.complex.faces] {n : ℕ} (p : Fin (n + 3) → D.sample → ℝ × V3) where
  x : Fin (n + 3) → E
  y : Fin (n + 3) → E
  chart : ∀ j, RawSourceCrossing e f S R (x j) (y j)
  source : ∀ j, MapsTo (fun z ↦ (D.inverse z : X)) (D.complex.closedStar (p j)).space
    (chart j).chart.source
  affine : ∀ j, (D.complex.closedStar (p j)).AffineOnFaces
    (fun z ↦ (chart j).chart (D.inverse z))
  axisChart : ∀ j z, z ∈ (D.complex.closedStar (p j)).space →
    (z ∈ D.axis.space ↔ (D.inverse z : X) ∈ R ∧
      (chart j).chart (D.inverse z) 0 = 0 ∧ (chart j).chart (D.inverse z) 1 = 0)
  sheetChart : ∀ j (k : Fin 2),
    ((D.complex.closedStar (p j)).vertexSubcomplex
      {z | (D.inverse z : X) ∈ R ∧ (chart j).chart (D.inverse z) k.castSucc = 0}).space =
    (D.complex.closedStar (p j)).space ∩
      {z | (D.inverse z : X) ∈ R ∧ (chart j).chart (D.inverse z) k.castSucc = 0}
  joint : ∀ j, signedTubeDiamond ≃ₜ
    (D.complex.barycentricDualBlock {p j, p (finRotate (n + 3) j)}).space
  jointPL : ∀ j, (joint j).IsFinitePL
  left : Fin (n + 3) → SignedAxisPermutation
  right : Fin (n + 3) → SignedAxisPermutation
  map : ∀ j, ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) 1) ≃ₜ
    (D.complex.barycentricDualBlock {p j}).space
  mapPL : ∀ j, (map j).IsFinitePL
  lower : ∀ j (z : signedTubeDiamond),
    (map j ⟨(z, 0), z.property, le_rfl, zero_le_one⟩ : D.sample → ℝ × V3) =
      joint ((finRotate (n + 3)).symm j) ((left j).diamond z)
  upper : ∀ j (z : signedTubeDiamond),
    (map j ⟨(z, 1), z.property, zero_le_one, le_rfl⟩ : D.sample → ℝ × V3) =
      joint j ((right j).diamond z)
  sheets : ∀ j k (z : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) 1)),
    (z : P2 × ℝ).1 ∈ signedTubeSheet k ↔ (chart j).chart (D.inverse (map j z)) k.castSucc = 0
  axis : ∀ j (z : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) 1)),
    (z : P2 × ℝ).1 = (0, 0) ↔ (map j z : D.sample → ℝ × V3) ∈ D.axis.space


end PoincareConjecture.M76.Dehn.Annuli

