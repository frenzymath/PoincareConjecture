import PoincareConjecture.Proofs.M76.Rigidity.OriginalCapHalfspaceCharts
import PoincareConjecture.Proofs.M76.Wall.ProtectedPLIntersection

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}

theorem OriginalDiskProduct.plDomain_cut (P : OriginalDiskProduct e R j)
    (hR : IsCompact R) (he : PLDomain e R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip)) :
    PLDomain e P.cutCarrier := by
  obtain ⟨hK, _, hfront, hoverlap, _, _⟩ := P.cut_geometry hR hopen
  have hC : IsClosed P.closedStrip :=
    (P.isCompact_closed_strip (by norm_num : (1 / 2 : ℝ) ≤ 1)).isClosed
  have hUC : P.openStrip ⊆ P.closedStrip :=
    image_mono (prod_mono subset_rfl Ioo_subset_Icc_self)
  refine ⟨he.cover, he.compatible, hK.isClosed, ?_⟩
  intro x hx
  by_cases hxC : x ∈ P.closedStrip
  · have hxE : x ∈ P.endDisks := hoverlap.subset ⟨hxC, hK.isClosed.frontier_subset hx⟩
    obtain ⟨w, hw, rfl⟩ := hxE
    obtain ⟨ell, v, B, hv, hwB, hzero, hcompat, hhalf, _⟩ :=
      P.exists_cap_halfspace_chart hR he hopen hw.2 ⟨w.1, hw.1⟩
    exact ⟨ell, v, B, hv, hwB, hzero, hcompat, hhalf⟩
  · have hxR : x ∈ frontier R := by
      rw [hfront] at hx
      rcases hx with hx | hx
      · exact hx.1
      · exact False.elim (hxC (hoverlap.symm.subset hx).1)
    obtain ⟨ell, v, H, hv, hxH, hzero, hcompat, hhalf⟩ := he.halfspace x hxR
    let B := H.restrOpen P.closedStripᶜ hC.isOpen_compl
    refine ⟨ell, v, B, hv, ⟨hxH, hxC⟩, hzero, ?_, ?_⟩
    · intro i
      exact (e i).piecewiseAffine_compatible_restrOpen_right H (hcompat i) hC.isOpen_compl
    · intro y hy
      change y ∈ R \ P.openStrip ↔ 0 ≤ ell (H y)
      constructor
      · intro h
        exact (hhalf y hy.1).mp h.1
      · intro h
        exact ⟨(hhalf y hy.1).mpr h, fun hyU => hy.2 (hUC hyU)⟩

end PoincareConjecture.M76
