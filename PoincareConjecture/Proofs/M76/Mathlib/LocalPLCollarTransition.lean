import PoincareConjecture.Proofs.M76.Mathlib.LocalPLAffineHalfspacePasting










set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





theorem LocallyPiecewiseAffineOn.collar_transition
    {T : E → E} {U : Set E} (hT : LocallyPiecewiseAffineOn T U)
    (a : E →L[ℝ] ℝ) (v : E)
    (hzero : ∀ x ∈ U, a x = 0 → a (T x) = 0) :
    let Z : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - a.smulRight v
    LocallyPiecewiseAffineOn
      (fun x => if 0 ≤ a x then T x else a x • v + Z (T (Z x)))
      (U ∩ Z ⁻¹' U) := by
  dsimp only
  let Z : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - a.smulRight v
  let V : Set E := U ∩ Z ⁻¹' U
  have hV : IsOpen V := hT.isOpen.inter (hT.isOpen.preimage Z.continuous)
  have hTZ : LocallyPiecewiseAffineOn (T ∘ Z) V :=
    (hT.comp (locallyPiecewiseAffineOn_affine Z.toContinuousAffineMap isOpen_univ)).mono
      hV (fun _ hx => ⟨mem_univ _, hx.2⟩)
  have hZTZ : LocallyPiecewiseAffineOn (Z ∘ (T ∘ Z)) V := by
    have h := (locallyPiecewiseAffineOn_affine Z.toContinuousAffineMap isOpen_univ).comp hTZ
    change LocallyPiecewiseAffineOn (Z ∘ (T ∘ Z)) (V ∩ (T ∘ Z) ⁻¹' univ) at h
    simpa only [preimage_univ, inter_univ] using h
  have hnormal : LocallyPiecewiseAffineOn (fun x => a x • v) V :=
    locallyPiecewiseAffineOn_affine (a.smulRight v).toContinuousAffineMap hV
  let addMap : E × E →L[ℝ] E :=
    ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E
  have hnegative : LocallyPiecewiseAffineOn (fun x => a x • v + Z (T (Z x))) V := by
    have h := (locallyPiecewiseAffineOn_affine addMap.toContinuousAffineMap isOpen_univ).comp
      (hnormal.prod_mk hZTZ)
    change LocallyPiecewiseAffineOn (fun x => a x • v + Z (T (Z x)))
      (V ∩ (fun x => (a x • v, Z (T (Z x)))) ⁻¹' univ) at h
    simpa only [preimage_univ, inter_univ] using h
  apply (hT.mono hV inter_subset_left).affine_halfspace_paste hnegative a.toLinearMap.toAffineMap
  intro x hx hax
  change a x = 0 at hax
  have hZx : Z x = x := by
    change x - a x • v = x
    rw [hax, zero_smul, sub_zero]
  have hTx : a (T x) = 0 := hzero x hx.1 hax
  change T x = a x • v + (T (Z x) - a (T (Z x)) • v)
  rw [hZx, hax, hTx, zero_smul, sub_zero, zero_add]

end Geometry
