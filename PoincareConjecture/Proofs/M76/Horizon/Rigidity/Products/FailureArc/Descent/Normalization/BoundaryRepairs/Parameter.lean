import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryRepairs.MovedComplexes
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryRepairs.SourceRegularity

set_option autoImplicit false
open Set Metric Geometry Topology unitInterval PLAnnularStrip

namespace Geometry.OriginalPLTower.PlanarAnnulusBoundaryMotion

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M} {s t : Stage e S f r C}
  {step : Step s t} {j : P2 → t.Carrier} {R Fmark : Set M}
  {a b : Ann} {W : Set s.Carrier} {ε : ℝ}
  (A : PlanarAnnulusBoundaryMotion step j R Fmark a b W ε)

theorem parameter_mem_closure_interior
    (hj : PolyhedralPLInCharts t.charts j Ann)
    (z : V3) (hz : z ∈ A.source.space) (hzJ : z ∈ interior A.support.space) :
    A.parameter z ∈ closure (interior (A.parameter '' A.source.space)) := by
  let T := A.window.right.trans A.chart
  let V := T.source ∩ T ⁻¹' interior A.support.space
  have hV : IsOpen V := T.isOpen_inter_preimage isOpen_interior
  have hpre : IsOpen ((fun x : Ann => j x) ⁻¹' V) :=
    hV.preimage hj.continuousOn.domRestrict
  obtain ⟨O, hO, hOpre⟩ := isOpen_induced_iff.mp hpre
  have hpoint : A.parameter z ∈ O := by
    have hxV : (⟨A.parameter z, A.parameter_range hz⟩ : Ann) ∈
        (fun x : Ann => j x) ⁻¹' V := by
      change j (A.parameter z) ∈ V
      refine ⟨(A.parameter_right z hz).1, ?_⟩
      change T (j (A.parameter z)) ∈ interior A.support.space
      rw [(A.parameter_right z hz).2]
      exact hzJ
    exact hOpre.symm.subset hxV
  have hcover : Ann ∩ O ⊆ A.parameter '' A.source.space := by
    intro x hx
    have hxV : j x ∈ V :=
      hOpre.subset (show (⟨x, hx.1⟩ : Ann) ∈ Subtype.val ⁻¹' O from hx.2)
    have hcoord : T (j x) ∈ A.source.space := A.source_space.symm.subset
      ⟨⟨j x, ⟨mem_image_of_mem j hx.1, hxV.1⟩, rfl⟩, interior_subset hxV.2⟩
    exact ⟨T (j x), hcoord, A.parameter_left x hx.1 hxV.1 (interior_subset hxV.2)⟩
  have hlocal : interior Ann ∩ O ⊆ interior (A.parameter '' A.source.space) :=
    interior_maximal (fun x hx => hcover ⟨interior_subset hx.1, hx.2⟩)
      (isOpen_interior.inter hO)
  apply closure_mono hlocal
  apply hO.closure_inter
  exact ⟨PoincareConjecture.M76.Dehn.Annuli.planar_annulus_subset_closure_interior
    (A.parameter_range hz), hpoint⟩

end Geometry.OriginalPLTower.PlanarAnnulusBoundaryMotion
