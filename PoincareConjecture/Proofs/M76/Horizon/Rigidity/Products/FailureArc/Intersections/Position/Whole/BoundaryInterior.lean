import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Whole.PairChart

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

def OriginalSurfacePairChart.interior_at
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S T : Set X} {y x : X}
    (C : OriginalSurfacePairChart e S T y true)
    (hx : x ∈ C.chart.source) (hxC : C.chart x ∈ C.coordinates.source)
    (hxS : x ∈ S) (hxT : x ∈ T)
    (hpositive : 0 < (C.coordinates (C.chart x)).1.2) :
    OriginalSurfacePairChart e S T x false := by
  let U : Set V3 := C.coordinates.source ∩
    C.coordinates ⁻¹' {z : C3 | 0 < z.1.2}
  have hU : IsOpen U := C.coordinates.isOpen_inter_preimage
    (isOpen_lt continuous_const (continuous_fst.snd))
  let H := C.coordinates.restr U
  have hHs : H.source = C.coordinates.source ∩ U := C.coordinates.restr_source' U hU
  let A : C3 ≃ᴬ[ℝ] C3 := ContinuousAffineEquiv.constVAdd ℝ C3
    (-(C.coordinates (C.chart x)))
  let B := H.trans A.toHomeomorph.toOpenPartialHomeomorph
  have hBsrc (z : V3) (hz : z ∈ B.source) : z ∈ C.coordinates.source ∧
      0 < (C.coordinates z).1.2 := by
    have hh : z ∈ H.source := hz.1
    exact ⟨(hHs.subset hh).1, (hHs.subset hh).2.2⟩
  have hzeroS : (C.coordinates (C.chart x)).2 = 0 := by
    have h := (C.first_surface (C.chart x) hxC).mp
      (by simpa only [C.chart.left_inv hx] using hxS)
    exact h.1
  have hzeroT : (C.coordinates (C.chart x)).1.1 = 0 := by
    have h := (C.second_surface (C.chart x) hxC).mp
      (by simpa only [C.chart.left_inv hx] using hxT)
    exact h.1
  refine {
    chart := C.chart
    coordinates := B
    compatible := C.compatible
    center_source := hx
    center_coordinates := ?_
    center_zero := ?_
    source_subset := fun z hz => C.source_subset (hBsrc z hz).1
    forwardPL := ?_
    inversePL := ?_
    first_surface := ?_
    second_surface := ?_ }
  · exact ⟨hHs.symm.subset ⟨hxC, hxC, hpositive⟩, mem_univ _⟩
  · change -(C.coordinates (C.chart x)) + C.coordinates (C.chart x) = 0
    exact neg_add_cancel _
  · exact (locallyPiecewiseAffineOn_affine A.toContinuousAffineMap isOpen_univ).comp
      (C.forwardPL.mono H.open_source (fun _ hz => (hHs.subset hz).1))
  · exact ((C.inversePL.mono H.open_target (fun _ hz => hz.1)).comp
      (locallyPiecewiseAffineOn_affine A.symm.toContinuousAffineMap isOpen_univ)).mono
        B.open_target (fun _ hz => ⟨mem_univ _, hz.2⟩)
  · intro z hz
    have h := C.first_surface z (hBsrc z hz).1
    have hpos := (hBsrc z hz).2.le
    change C.chart.symm z ∈ S ↔
      (-(C.coordinates (C.chart x)) + C.coordinates z).2 = 0 ∧ (false = true → _)
    simpa only [Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, hzeroS,
      neg_zero, zero_add, Bool.false_eq_true, IsEmpty.forall_iff, and_true,
      true_implies, hpos] using h
  · intro z hz
    have h := C.second_surface z (hBsrc z hz).1
    have hpos := (hBsrc z hz).2.le
    change C.chart.symm z ∈ T ↔
      (-(C.coordinates (C.chart x)) + C.coordinates z).1.1 = 0 ∧ (false = true → _)
    simpa only [Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, hzeroT,
      neg_zero, zero_add, Bool.false_eq_true, IsEmpty.forall_iff, and_true,
      true_implies, hpos] using h

end PoincareConjecture.M76
