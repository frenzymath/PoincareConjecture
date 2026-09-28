import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryCharts.Source
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Reduction.SourceGeometry



set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1



theorem planar_annulus_subset_closure_interior : Ann ⊆ closure (interior Ann) := by
  intro x hx
  by_cases hi : x ∈ interior Ann
  · exact subset_closure hi
  have hf : x ∈ frontier Ann := ⟨subset_closure hx, hi⟩
  obtain ⟨H, B, hxH, _, hB, _, _, hhalf, _⟩ :=
    PoincareConjecture.M76.Dehn.exists_planar_annulus_boundary_chart hx
      ((mem_frontier_planar_annulus_iff x).mp hf)
  let ell : P2 →ᴬ[ℝ] ℝ := B.toContinuousLinearMap.toContinuousAffineMap
  have hopen : IsOpenMap (ell : P2 → ℝ) := ell.toAffineMap.isOpenMap ell.continuous
    (ell.toAffineMap.linear_surjective_iff.mp (LinearMap.surjective hB))
  have hreg : closure (interior ((ell : P2 → ℝ) ⁻¹' Ici 0)) =
      (ell : P2 → ℝ) ⁻¹' Ici 0 := by
    rw [← hopen.preimage_interior_eq_interior_preimage ell.continuous, interior_Ici,
      ← hopen.preimage_closure_eq_closure_preimage ell.continuous, closure_Ioi]
  have himage : H.IsImage Ann ((ell : P2 → ℝ) ⁻¹' Ici 0) :=
    fun {y} hy => (hhalf y hy).symm
  have hh := himage.interior.closure.apply_mem_iff hxH
  rw [hreg] at hh
  exact hh.mp ((himage.apply_mem_iff hxH).mpr hx)

theorem closure_interior_planar_annulus : closure (interior Ann) = Ann :=
  Subset.antisymm
    (closure_minimal interior_subset isCompact_planar_annulus.isClosed)
    planar_annulus_subset_closure_interior

end PoincareConjecture.M76.Dehn.Annuli
