import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.ExteriorDiskLocalCut
import PoincareConjecture.Proofs.M76.Wall.PLDomainComponents
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonWallComplementBall

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem OriginalDiskProduct.exterior_attachment_geometry
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {K H L : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e L j)
    (he : PLDomain e K) (hK : IsCompact K)
    (hKH : K ⊆ interior H) (hL : L = H ∩ (interior K)ᶜ)
    (hLfront : frontier L = frontier K ∪ (frontier H ∩ (interior K)ᶜ))
    (hstripH : P.closedStrip ⊆ interior H)
    (hcutPL : PLDomain e P.cutCarrier)
    (hint : interior P.cutCarrier = interior L \ P.closedStrip)
    (hcutfront : frontier P.cutCarrier = (frontier L \ P.openStrip) ∪ P.endDisks)
    (hoverlap : P.closedStrip ∩ P.cutCarrier = P.endDisks) :
    PLDomain e (K ∪ P.closedStrip) ∧ IsCompact (K ∪ P.closedStrip) ∧
      K ∪ P.closedStrip ⊆ interior H ∧
      K ∪ P.closedStrip = (interior P.cutCarrier)ᶜ ∩ interior H ∧
      frontier (K ∪ P.closedStrip) = (frontier K \ P.openStrip) ∪ P.endDisks := by
  have hstripcompact : IsCompact P.closedStrip :=
    P.isCompact_closed_strip (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hJcompact := hK.union hstripcompact
  have hJH : K ∪ P.closedStrip ⊆ interior H := union_subset hKH hstripH
  have hintL : interior L = interior H ∩ Kᶜ := by
    rw [hL, interior_inter, interior_compl, he.closure_interior]
  have hJeq : K ∪ P.closedStrip = (interior P.cutCarrier)ᶜ ∩ interior H := by
    rw [hint, hintL]
    ext x
    constructor
    · intro hx
      refine ⟨?_, hJH hx⟩
      rintro ⟨⟨_, hxK⟩, hxstrip⟩
      exact hx.elim hxK hxstrip
    · rintro ⟨hxnot, hxH⟩
      by_cases hxK : x ∈ K
      · exact Or.inl hxK
      · exact Or.inr (by
          by_contra hxstrip
          exact hxnot ⟨⟨hxH, hxK⟩, hxstrip⟩)
  obtain ⟨hopp, hoppfront⟩ := hcutPL.compl_interior
  have hJsub : K ∪ P.closedStrip ⊆ (interior P.cutCarrier)ᶜ := by
    rw [hJeq]
    exact inter_subset_left
  have hJopen : IsOpen ((Subtype.val : {x // x ∉ interior P.cutCarrier} → X) ⁻¹'
      (K ∪ P.closedStrip)) := by
    have heq : (Subtype.val : {x // x ∉ interior P.cutCarrier} → X) ⁻¹'
        (K ∪ P.closedStrip) = (Subtype.val : {x // x ∉ interior P.cutCarrier} → X) ⁻¹' interior H := by
      ext x
      rw [hJeq]
      exact and_iff_right x.property
    rw [heq]
    exact isOpen_interior.preimage continuous_subtype_val
  have hJPL := hopp.of_relative_clopen_subset hJsub hJcompact.isClosed hJopen
  refine ⟨hJPL, hJcompact, hJH, hJeq, ?_⟩
  rw [Set.frontier_eq_inter_of_eq_inter_open hopp.closed hJcompact.isClosed
    isOpen_interior hJeq, hoppfront, hcutfront, hLfront]
  ext x
  constructor
  · rintro ⟨hxJ, (⟨hxK | hxH, hxnot⟩ | hxend)⟩
    · exact Or.inl ⟨hxK, hxnot⟩
    · exact False.elim (hxH.1.2 (hJH hxJ))
    · exact Or.inr hxend
  · rintro (⟨hxK, hxnot⟩ | hxend)
    · exact ⟨Or.inl (he.closed.frontier_subset hxK), Or.inl ⟨Or.inl hxK, hxnot⟩⟩
    · exact ⟨Or.inr (hoverlap.symm ▸ hxend).1, Or.inr hxend⟩

theorem OriginalDiskProduct.exterior_attachment_geometry_with_collars
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {K H L : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e L j)
    (he : PLDomain e K) (hK : IsCompact K)
    (hKH : K ⊆ interior H) (hL : L = H ∩ (interior K)ᶜ)
    (hLfront : frontier L = frontier K ∪ (frontier H ∩ (interior K)ᶜ))
    (hstripH : P.closedStrip ⊆ interior H)
    (hcutPL : PLDomain e P.cutCarrier)
    (hint : interior P.cutCarrier = interior L \ P.closedStrip)
    (hcutfront : frontier P.cutCarrier = (frontier L \ P.openStrip) ∪ P.endDisks)
    (hoverlap : P.closedStrip ∩ P.cutCarrier = P.endDisks)
    (hcollars : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      IsOpen ((Subtype.val : L → X) ⁻¹'
        (P.map '' (closedBall (0 : V2) 1 ×ˢ Ioo (-ε) ε))) ∧
      IsOpen ((Subtype.val : frontier L → X) ⁻¹'
        (P.map '' (sphere (0 : V2) 1 ×ˢ Ioo (-ε) ε)))) :
    PLDomain e (K ∪ P.closedStrip) ∧ IsCompact (K ∪ P.closedStrip) ∧
      K ∪ P.closedStrip ⊆ interior H ∧
      K ∪ P.closedStrip = (interior P.cutCarrier)ᶜ ∩ interior H ∧
      frontier (K ∪ P.closedStrip) = (frontier K \ P.openStrip) ∪ P.endDisks ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        IsOpen ((Subtype.val : L → X) ⁻¹'
          (P.map '' (closedBall (0 : V2) 1 ×ˢ Ioo (-ε) ε))) ∧
        IsOpen ((Subtype.val : frontier L → X) ⁻¹'
          (P.map '' (sphere (0 : V2) 1 ×ˢ Ioo (-ε) ε))) ∧
        IsOpen ((Subtype.val : frontier K → X) ⁻¹'
          (P.map '' (sphere (0 : V2) 1 ×ˢ Ioo (-ε) ε))) := by
  obtain ⟨hPL, hcompact, hsub, heq, hfront⟩ :=
    P.exterior_attachment_geometry he hK hKH hL hLfront hstripH
      hcutPL hint hcutfront hoverlap
  refine ⟨hPL, hcompact, hsub, heq, hfront, ?_⟩
  intro ε hε hε1
  obtain ⟨hopen, hlateral⟩ := hcollars ε hε hε1
  refine ⟨hopen, hlateral, ?_⟩
  let inclusion : frontier K → frontier L :=
    fun x => ⟨x, hLfront.symm.subset (Or.inl x.property)⟩
  have hcontinuous : Continuous inclusion :=
    continuous_subtype_val.subtype_mk _
  exact hlateral.preimage hcontinuous

end PoincareConjecture.M76
