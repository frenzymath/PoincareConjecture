import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SphereExteriorSurfaceGerms
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.CompatibleChartLabels

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

theorem coordinate_crossings_of_original_paired_charts
    {X α : Type*} [TopologicalSpace X]
    {e : α → OpenPartialHomeomorph X V3} {R S F : Set X}
    (he : PLDomain e R) (hSR : S ⊆ interior R)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i,(e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (hCQ : S ∩ F ⊆ Q.source)
    (hcross : ∀ x ∈ S ∩ F,∃ H : OpenPartialHomeomorph X V3,
      x ∈ H.source ∧ H x = 0 ∧
      (∀ i,(e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ H.source,y ∈ S ↔ H y 1 = 0) ∧
      ∀ y ∈ H.source,y ∈ F ↔ H y 0 = 0) :
    ∀ w ∈ Q '' (S ∩ F),∀ O : Set V3,IsOpen O → w ∈ O →
      ∃ C : OpenPartialHomeomorph V3 C3,
        w ∈ C.source ∧ C.source ⊆ O ∩ Q.target ∧
        (∀ z ∈ C.source,Q.symm z ∈ interior R) ∧ C w = 0 ∧
        LocallyPiecewiseAffineOn C C.source ∧
        LocallyPiecewiseAffineOn C.symm C.target ∧
        (∀ y ∈ C.source,Q.symm y ∈ S ↔ (C y).2 = 0) ∧
        ∀ y ∈ C.source,Q.symm y ∈ F ↔ (C y).1.1 = 0 := by
  rintro w ⟨x,hx,rfl⟩ O hO hxO
  obtain ⟨H,hxH,hH0,hHe,hHS,hHF⟩ := hcross x hx
  let A := Q.symm.trans H
  have hA : A ∈ piecewiseAffineGroupoid V3 :=
    compatiblePLCharts_trans e he.cover he.compatible Q H hQ hHe
  let U := O ∩ (Q.target ∩ Q.symm ⁻¹' interior R)
  have hU : IsOpen U := hO.inter (Q.symm.isOpen_inter_preimage isOpen_interior)
  let B := A.restrOpen U hU
  have hB : LocallyPiecewiseAffineOn B B.source :=
    hA.1.mono B.open_source inter_subset_left
  let C := B.trans crossingCoordinateOrder.symm.toHomeomorph.toOpenPartialHomeomorph
  have hC : LocallyPiecewiseAffineOn C C.source :=
    (locallyPiecewiseAffineOn_affine crossingCoordinateOrder.symm.toContinuousAffineMap
      isOpen_univ).comp hB
  have hxQ := hCQ hx
  have hxC : Q x ∈ C.source := by
    refine ⟨⟨⟨Q.map_source hxQ,?_⟩,hxO,Q.map_source hxQ,?_⟩,mem_univ _⟩
    · change Q.symm (Q x) ∈ H.source
      rw [Q.left_inv hxQ]
      exact hxH
    · simpa only [mem_preimage,Q.left_inv hxQ] using hSR hx.1
  refine ⟨C,hxC,fun y hy => ⟨hy.1.2.1,hy.1.2.2.1⟩,
    fun y hy => hy.1.2.2.2,?_,hC,C.locallyPiecewiseAffineOn_symm hC,?_,?_⟩
  · change crossingCoordinateOrder.symm (H (Q.symm (Q x))) = 0
    rw [Q.left_inv hxQ,hH0]
    rfl
  · intro y hy
    exact hHS (Q.symm y) hy.1.1.2
  · intro y hy
    exact hHF (Q.symm y) hy.1.1.2

end PoincareConjecture.M76
