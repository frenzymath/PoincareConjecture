import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Construction.TubeAndStrips








set_option autoImplicit false

open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductPieces

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

theorem isCompact_pieceBottom_union
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R W Q : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X} {j : Bool → V2 → X}
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (P : ∀ b, OriginalDiskProduct e Q (j b))
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    IsCompact (⋃ i, range (pieceBottom U P r i)) := by
  apply isCompact_iUnion
  intro i
  let : CompactSpace (pieceBase r i) :=
    isCompact_iff_compactSpace.mp (by
      cases i <;> exact isCompact_Icc.prod isCompact_Icc)
  have hpl : PolyhedralPLInCharts e (pieceMap U P i) (pieceBase r i ×ˢ I) := by
    cases i with
    | none => exact (tubePiece_properties U hr hr1).1
    | some b => exact (diskStrip_properties (P b)).1
  have hc : Continuous (pieceBottom U P r i) :=
    hpl.continuousOn.comp_continuous
      (continuous_subtype_val.prodMk continuous_const)
      (fun z => ⟨z.property, by norm_num⟩)
  exact isCompact_range hc

end PoincareConjecture.M76.Dehn.Annuli.ProductPieces
