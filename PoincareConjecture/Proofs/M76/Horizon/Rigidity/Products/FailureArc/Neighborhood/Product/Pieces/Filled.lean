import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Construction.TubeAndStrips
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.AnnularParameter.PairDisk



set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductPieces
open TubeExterior PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Disk" => closedBall (0 : P2) 1

def filledPieceBase (r : ℝ) : Option (Option Bool) → Set P2
  | none => Disk
  | some i => pieceBase r i

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R W Q : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X} {j : Bool → V2 → X}

def filledPieceMap (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (P : ∀ b, OriginalDiskProduct e Q (j b)) (k : P2 × ℝ → X) :
    Option (Option Bool) → P2 × ℝ → X
  | none => k
  | some i => pieceMap U P i

theorem exists_filledPieceBase_triangulation {r : ℝ} (hr : 0 < r)
    (i : Option (Option Bool)) :
    ∃ K : SimplicialComplex ℝ P2, K.faces.Finite ∧ K.space = filledPieceBase r i := by
  have hball : ∃ q : Set P2, IsFinitePLBallPair P2 (filledPieceBase r i) q := by
    cases i with
    | none => exact ⟨_, AnnularParameter.pairDisk_isFinitePLBallPair⟩
    | some i =>
      cases i with
      | none =>
        exact ⟨_, (isFinitePLBallPair_Icc (by linarith : -r < r)).prod
          (isFinitePLBallPair_Icc (by linarith : -r < r))⟩
      | some b =>
        exact ⟨_, (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1)).prod
          (isFinitePLBallPair_Icc (by norm_num : -(1/2 : ℝ) < 1/2))⟩
  obtain ⟨_, _, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hball
  exact ⟨K, hK, hKs⟩

theorem filledPieceMap_properties
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (P : ∀ b, OriginalDiskProduct e Q (j b))
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) {k : P2 × ℝ → X}
    (hk : PolyhedralPLInCharts e k (Disk ×ˢ I)) (hki : InjOn k (Disk ×ˢ I))
    (i : Option (Option Bool)) :
    PolyhedralPLInCharts e (filledPieceMap U P k i) (filledPieceBase r i ×ˢ I) ∧
      InjOn (filledPieceMap U P k i) (filledPieceBase r i ×ˢ I) := by
  cases i with
  | none => exact ⟨hk, hki⟩
  | some i =>
    have h : PolyhedralPLInCharts e (pieceMap U P i) (pieceBase r i ×ˢ I) ∧
        IsEmbedding (fun p : pieceBase r i ×ˢ I => pieceMap U P i p) := by
      cases i with
      | none => exact ⟨(tubePiece_properties U hr hr1).1, (tubePiece_properties U hr hr1).2.1⟩
      | some b => exact ⟨(diskStrip_properties (P b)).1, (diskStrip_properties (P b)).2.1⟩
    refine ⟨h.1, ?_⟩
    intro x hx y hy hxy
    exact congrArg Subtype.val (h.2.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)

omit [T2Space X] in
theorem filledPieceMap_bottom_image
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (P : ∀ b, OriginalDiskProduct e Q (j b)) (k : P2 × ℝ → X) (r : ℝ) :
    (⋃ i, filledPieceMap U P k i '' (filledPieceBase r i ×ˢ {(0 : ℝ)})) =
      (⋃ i, range (pieceBottom U P r i)) ∪ k '' (Disk ×ˢ {(0 : ℝ)}) := by
  ext x
  constructor
  · intro hx
    rcases mem_iUnion.mp hx with ⟨i, ⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
    have ht' : t = 0 := ht
    subst t
    cases i with
    | none => exact Or.inr ⟨(z, 0), ⟨hz, rfl⟩, rfl⟩
    | some i => exact Or.inl (mem_iUnion.mpr ⟨i, ⟨z, hz⟩, rfl⟩)
  · rintro (hx | hx)
    · rcases mem_iUnion.mp hx with ⟨i, z, rfl⟩
      exact mem_iUnion.mpr ⟨some i, (z, 0), ⟨z.property, rfl⟩, rfl⟩
    · exact mem_iUnion.mpr ⟨none, hx⟩

end PoincareConjecture.M76.Dehn.Annuli.ProductPieces
