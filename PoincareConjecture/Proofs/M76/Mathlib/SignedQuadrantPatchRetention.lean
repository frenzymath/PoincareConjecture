import PoincareConjecture.Proofs.M76.Mathlib.FrontierPatchConeNeighborhood












set_option autoImplicit false

open Set Geometry

namespace CoordinateHalfBoxes




def signedRectangle (r : ℝ) (i : Bool × Bool) : Set (ℝ × ℝ) :=
  uIcc 0 (if i.1 then -r else r) ×ˢ uIcc 0 (if i.2 then -r else r)

private theorem mem_Icc_iff_mem_signedInterval {r x : ℝ} (hr : 0 ≤ r) :
    x ∈ Icc (-r) r ↔ ∃ i : Bool, x ∈ uIcc 0 (if i then -r else r) := by
  constructor
  · intro hx
    by_cases hx0 : x ≤ 0
    · refine ⟨true, ?_⟩
      change x ∈ uIcc 0 (-r)
      rw [uIcc_of_ge (neg_nonpos.mpr hr)]
      exact ⟨hx.1, hx0⟩
    · refine ⟨false, ?_⟩
      change x ∈ uIcc 0 r
      rw [uIcc_of_le hr]
      exact ⟨(lt_of_not_ge hx0).le, hx.2⟩
  · rintro ⟨i, hi⟩
    cases i
    · change x ∈ uIcc 0 r at hi
      rw [uIcc_of_le hr] at hi
      exact ⟨(neg_nonpos.mpr hr).trans hi.1, hi.2⟩
    · change x ∈ uIcc 0 (-r) at hi
      rw [uIcc_of_ge (neg_nonpos.mpr hr)] at hi
      exact ⟨hi.1, hi.2.trans hr⟩




theorem base_eq_iUnion_signedRectangle {r : ℝ} (hr : 0 ≤ r) :
    base r = ⋃ i : Bool × Bool, signedRectangle r i := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := (mem_Icc_iff_mem_signedInterval hr).mp hx.1
    obtain ⟨j, hj⟩ := (mem_Icc_iff_mem_signedInterval hr).mp hx.2
    exact mem_iUnion.mpr ⟨(i, j), hi, hj⟩
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact ⟨(mem_Icc_iff_mem_signedInterval hr).mpr ⟨i.1, hi.1⟩,
      (mem_Icc_iff_mem_signedInterval hr).mpr ⟨i.2, hi.2⟩⟩




theorem image_base_eq_iUnion_signedRectangle {E : Type*}
    (ψ : (ℝ × ℝ) → E) {r : ℝ} (hr : 0 ≤ r) :
    ψ '' base r = ⋃ i : Bool × Bool, ψ '' signedRectangle r i := by
  rw [base_eq_iUnion_signedRectangle hr, image_iUnion]




theorem cone_image_base_eq_iUnion_signedRectangle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : (ℝ × ℝ) → E) {r : ℝ} (hr : 0 ≤ r) :
    convexJoin ℝ {0} (ψ '' base r) =
      ⋃ i : Bool × Bool, convexJoin ℝ {0} (ψ '' signedRectangle r i) := by
  rw [image_base_eq_iUnion_signedRectangle ψ hr, convexJoin_iUnion_right]




theorem eqOn_image_base_of_signedRectangles {E F : Type*} {S : Set E}
    (ψ : (ℝ × ℝ) → E) (g : S → F) (L : E → F) {r : ℝ} (hr : 0 ≤ r)
    (hkeep : ∀ i : Bool × Bool, ∀ x : S,
      (x : E) ∈ ψ '' signedRectangle r i → g x = L x) :
    ∀ x : S, (x : E) ∈ ψ '' base r → g x = L x := by
  intro x hx
  rw [image_base_eq_iUnion_signedRectangle ψ hr] at hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  exact hkeep i x hi

end CoordinateHalfBoxes

open CoordinateHalfBoxes






theorem ContinuousAffineEquiv.exists_box_eq_linear_of_signed_quadrant_cones
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E)
    {C O : Set E} (hcv : Convex ℝ C) (hzero : (0 : E) ∈ interior C)
    {p q : E} (hf0 : f 0 = p) (hq : q ∈ frontier C)
    {ρ : ℝ} (hρ : 1 < ρ) (hqp : q = ρ • p)
    (ψ : (ℝ × ℝ) → E) {r : ℝ} (hr : 0 ≤ r)
    (hO : IsOpen O) (hqO : q ∈ O) (hOP : frontier C ∩ O ⊆ ψ '' base r)
    (g : C → F) (L : E →ₗ[ℝ] F)
    (hkeep : ∀ i : Bool × Bool, ∀ x : C,
      (x : E) ∈ convexJoin ℝ {0} (ψ '' signedRectangle r i) → g x = L x) :
    ∃ δ : ℝ, 0 < δ ∧ f '' box δ ⊆ interior C ∧
      ∀ x : C, (x : E) ∈ f '' box δ → g x = L x := by
  obtain ⟨δ, hδ, hbox⟩ := f.exists_box_in_frontier_patch_cone
    hcv hzero hf0 hq hρ hqp hO hqO hOP
  refine ⟨δ, hδ, fun x hx => (hbox hx).1, ?_⟩
  intro x hx
  have hxcone := (hbox hx).2
  rw [cone_image_base_eq_iUnion_signedRectangle ψ hr] at hxcone
  obtain ⟨i, hi⟩ := mem_iUnion.mp hxcone
  exact hkeep i x hi
