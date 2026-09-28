import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Lift.Cutoff

noncomputable section
set_option autoImplicit false

open Set Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)

theorem exists_parametric_height_cutoff_lift_product
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hΦ : ContDiff Real ∞ (fun q : Real × Real × E2 => Φ q.1 q.2.1 q.2.2))
    (hΦinv : ContDiff Real ∞ (fun q : Real × Real × E2 => (Φ q.1 q.2.1).symm q.2.2))
    (χ : Real → Real) (hχ : ContDiff Real ∞ χ) :
    ∃ P : Diffeomorph 𝓘(Real, Real × E2) 𝓘(Real, Real × E2)
        (Real × E2) (Real × E2) ∞,
      (∀ z, P z = (z.1, Φ (χ z.1) z.1 z.2)) ∧
      (∀ z, P.symm z = (z.1, (Φ (χ z.1) z.1).symm z.2)) := by
  exact exists_height_cutoff_lift_product (fun z => Φ (χ z) z)
    (hΦ.comp ((hχ.comp contDiff_fst).prodMk contDiff_id))
    (hΦinv.comp ((hχ.comp contDiff_fst).prodMk contDiff_id)) id contDiff_id

theorem exists_parametric_height_cutoff_lift
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (h0 : ∀ z x, Φ 0 z x = x)
    (hΦ : ContDiff Real ∞ (fun q : Real × Real × E2 => Φ q.1 q.2.1 q.2.2))
    (hΦinv : ContDiff Real ∞ (fun q : Real × Real × E2 => (Φ q.1 q.2.1).symm q.2.2))
    {K : Set E2} (hsupp : ∀ t z x, x ∉ K → Φ t z x = x)
    (χ : Real → Real) (hχ : ContDiff Real ∞ χ) :
    ∃ H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ y, H y = toE3 (Φ (χ (y 2)) (y 2) (toE2 y)) (y 2)) ∧
      (∀ y, H.symm y = toE3 ((Φ (χ (y 2)) (y 2)).symm (toE2 y)) (y 2)) ∧
      (∀ y, (H y) 2 = y 2) ∧
      (∀ (S : Set E2) (c : Real), H '' slice S c = slice (Φ (χ c) c '' S) c) ∧
      (∀ y, toE2 y ∉ K → H y = y) ∧
      (∀ y, χ (y 2) = 0 → H y = y) := by
  obtain ⟨H, hH, hHi, hh, hs⟩ := exists_height_lift (fun z => Φ (χ z) z)
    (hΦ.comp ((hχ.comp contDiff_fst).prodMk contDiff_id))
    (hΦinv.comp ((hχ.comp contDiff_fst).prodMk contDiff_id))
  have hcoord (y : E3) : toE3 (toE2 y) (y 2) = y := by
    ext i
    fin_cases i <;> rfl
  refine ⟨H, hH, hHi, hh, hs, ?_, ?_⟩
  · intro y hy
    rw [hH, hsupp _ _ _ hy, hcoord]
  · intro y hy
    rw [hH, hy, h0, hcoord]

theorem image_iUnion_slice_parametric
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (χ : Real → Real) {I : Set Real} (L : Real → Set E2)
    (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ (S : Set E2) (c : Real), H '' slice S c =
      slice (Φ (χ c) c '' S) c) :
    H '' (⋃ c ∈ I, slice (L c) c) =
      ⋃ c ∈ I, slice (Φ (χ c) c '' L c) c := by
  exact image_iUnion_slice (fun c => Φ (χ c) c) id L H hH

theorem image_iUnion_slice_parametric_of_eq_one
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (χ : Real → Real) {I : Set Real} (L : Real → Set E2)
    (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ (S : Set E2) (c : Real), H '' slice S c =
      slice (Φ (χ c) c '' S) c)
    (hχ : ∀ c ∈ I, χ c = 1) :
    H '' (⋃ c ∈ I, slice (L c) c) =
      ⋃ c ∈ I, slice (Φ 1 c '' L c) c := by
  rw [image_iUnion_slice_parametric Φ χ L H hH]
  apply iUnion_congr
  intro c
  apply iUnion_congr
  intro hc
  rw [hχ c hc]

theorem image_iUnion_slice_parametric_of_matching
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (χ : Real → Real) {I : Set Real} (L M : Real → Set E2)
    (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ (S : Set E2) (c : Real), H '' slice S c =
      slice (Φ (χ c) c '' S) c)
    (hχ : ∀ c ∈ I, χ c = 1)
    (hmatch : ∀ c ∈ I, Φ 1 c '' L c = M c) :
    H '' (⋃ c ∈ I, slice (L c) c) = ⋃ c ∈ I, slice (M c) c := by
  rw [image_iUnion_slice_parametric_of_eq_one Φ χ L H hH hχ]
  apply iUnion_congr
  intro c
  apply iUnion_congr
  intro hc
  rw [hmatch c hc]

end Poincare.Manifold.Schoenflies.Saddle
