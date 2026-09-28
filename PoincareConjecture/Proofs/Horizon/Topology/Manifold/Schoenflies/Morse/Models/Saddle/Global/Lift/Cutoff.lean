import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.FilledModel
import PoincareConjecture.Proofs.Horizon.Analysis.InnerProductSpace.Coordinates.FinSucc








noncomputable section
set_option autoImplicit false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev P2 := Real × E2

def toE2 (y : E3) : E2 := WithLp.toLp 2 ![y 0, y 1]

def toE3 (x : E2) (c : Real) : E3 := WithLp.toLp 2 ![x 0, x 1, c]

private theorem toE2_toE3 (x : E2) (c : Real) : toE2 (toE3 x c) = x := by
  ext i
  fin_cases i <;> rfl

private theorem toE3_toE2 (y : E3) : toE3 (toE2 y) (y 2) = y := by
  ext i
  fin_cases i <;> rfl

private theorem toE3_height (x : E2) (c : Real) : (toE3 x c) 2 = c := rfl

def slice (S : Set E2) (c : Real) : Set E3 :=
  {y | toE2 y ∈ S ∧ y 2 = c}

private def coordinateEquiv : E3 ≃L[Real] (Real × E2) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun y => (y 2, toE2 y)
      invFun := fun z => toE3 z.2 z.1
      left_inv := by
        intro y
        ext i
        fin_cases i <;> rfl
      right_inv := by
        intro z
        apply Prod.ext
        · rfl
        · ext i
          fin_cases i <;> rfl
      map_add' := by
        intro y z
        apply Prod.ext
        · simp
        · ext i
          fin_cases i <;> simp [toE2]
      map_smul' := by
        intro c y
        apply Prod.ext
        · simp
        · ext i
          fin_cases i <;> simp [toE2] }

private theorem coordinateEquiv_apply (y : E3) :
    coordinateEquiv y = (y 2, toE2 y) := by
  rfl

private theorem coordinateEquiv_symm_apply (z : P2) :
    coordinateEquiv.symm z = toE3 z.2 z.1 := by
  rfl



theorem exists_height_lift
    (Φ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hΦ : ContDiff Real ∞ (fun z : Real × E2 => Φ z.1 z.2))
    (hΦinv : ContDiff Real ∞ (fun z : Real × E2 => (Φ z.1).symm z.2)) :
    ∃ H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ y : E3, H y = toE3 (Φ (y 2) (toE2 y)) (y 2)) ∧
      (∀ y : E3, H.symm y = toE3 ((Φ (y 2)).symm (toE2 y)) (y 2)) ∧
      (∀ y : E3, (H y) 2 = y 2) ∧
      (∀ (S : Set E2) (c : Real), H '' (slice S c) =
        slice (Φ c '' S) c) := by
  let P : Diffeomorph
      𝓘(Real, P2) 𝓘(Real, P2) P2 P2 ∞ := {
    toEquiv := {
      toFun := fun z => (z.1, Φ z.1 z.2)
      invFun := fun z => (z.1, (Φ z.1).symm z.2)
      left_inv := by intro z; simp
      right_inv := by intro z; simp }
    contMDiff_toFun := by
      apply ContDiff.contMDiff
      exact contDiff_fst.prodMk hΦ
    contMDiff_invFun := by
      apply ContDiff.contMDiff
      exact contDiff_fst.prodMk hΦinv }
  let C : Diffeomorph 𝓘(Real, P2) (𝓡 3) P2 E3 ∞ :=
    coordinateEquiv.symm.toDiffeomorph
  let H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ := (C.symm.trans P).trans C
  have hC (z : P2) : C z = toE3 z.2 z.1 := by
    change coordinateEquiv.symm z = _
    exact coordinateEquiv_symm_apply z
  have hCs (y : E3) : C.symm y = (y 2, toE2 y) := by
    change coordinateEquiv y = _
    exact coordinateEquiv_apply y
  have hH (y : E3) : H y =
      toE3 (Φ (y 2) (toE2 y)) (y 2) := by
    change C (P (C.symm y)) = _
    rw [hCs]
    exact hC _
  refine ⟨H, hH, ?_, ?_, ?_⟩
  · intro y
    change C (P.symm (C.symm y)) = _
    rw [hCs]
    exact hC _
  · intro y
    rw [hH]
    rfl
  · intro S c
    ext y
    constructor
    · rintro ⟨x, ⟨hxS, hxc⟩, rfl⟩
      rw [hH]
      rw [hxc]
      refine ⟨⟨toE2 x, hxS, ?_⟩, ?_⟩
      · exact (toE2_toE3 _ _).symm
      · rfl
    · rintro ⟨hy, hyc⟩
      obtain ⟨x, hx, hxy⟩ := hy
      refine ⟨toE3 x c, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · simpa only [toE2_toE3] using hx
        · exact toE3_height x c
      · rw [hH]
        simp only [toE3_height, toE2_toE3]
        rw [hxy, ← hyc]
        exact toE3_toE2 y


theorem exists_height_cutoff_lift
    (Φ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (h0 : ∀ x, Φ 0 x = x)
    (hΦ : ContDiff Real ∞ (fun z : Real × E2 => Φ z.1 z.2))
    (hΦinv : ContDiff Real ∞ (fun z : Real × E2 => (Φ z.1).symm z.2))
    {K : Set E2} (hK : IsCompact K)
    (hsupp : ∀ t x, x ∉ K → Φ t x = x)
    (χ : Real → Real) (hχ : ContDiff Real ∞ χ) :
    ∃ H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ y : E3, H y = toE3 (Φ (χ (y 2)) (toE2 y)) (y 2)) ∧
      (∀ y : E3, (H y) 2 = y 2) ∧
      (∀ (S : Set E2) (c : Real), H '' (slice S c) =
        slice (Φ (χ c) '' S) c) ∧
      (∀ y : E3, toE2 y ∉ K → H y = y) := by
  obtain ⟨H, hH, _, hheight, hslice⟩ := exists_height_lift (fun z => Φ (χ z))
    (hΦ.comp ((hχ.comp contDiff_fst).prodMk contDiff_snd))
    (hΦinv.comp ((hχ.comp contDiff_fst).prodMk contDiff_snd))
  refine ⟨H, hH, hheight, hslice, ?_⟩
  intro y hy
  rw [hH, hsupp _ _ hy]
  exact toE3_toE2 y


theorem exists_height_cutoff_lift_product
    (Φ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hΦ : ContDiff Real ∞ (fun z : Real × E2 => Φ z.1 z.2))
    (hΦinv : ContDiff Real ∞ (fun z : Real × E2 => (Φ z.1).symm z.2))
    (χ : Real → Real) (hχ : ContDiff Real ∞ χ) :
    ∃ P : Diffeomorph 𝓘(Real, P2) 𝓘(Real, P2) P2 P2 ∞,
      (∀ z : P2, P z = (z.1, Φ (χ z.1) z.2)) ∧
      (∀ z : P2, P.symm z = (z.1, (Φ (χ z.1)).symm z.2)) := by
  let P : Diffeomorph 𝓘(Real, P2) 𝓘(Real, P2) P2 P2 ∞ := {
    toEquiv := {
      toFun := fun z => (z.1, Φ (χ z.1) z.2)
      invFun := fun z => (z.1, (Φ (χ z.1)).symm z.2)
      left_inv := by intro z; simp
      right_inv := by intro z; simp }
    contMDiff_toFun := by
      apply ContDiff.contMDiff
      exact contDiff_fst.prodMk
        (hΦ.comp ((hχ.comp contDiff_fst).prodMk contDiff_snd))
    contMDiff_invFun := by
      apply ContDiff.contMDiff
      exact contDiff_fst.prodMk
        (hΦinv.comp ((hχ.comp contDiff_fst).prodMk contDiff_snd)) }
  exact ⟨P, fun z => rfl, fun z => rfl⟩

theorem image_iUnion_slice
    (Φ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (χ : Real → Real) {I : Set Real} (L : Real → Set E2)
    (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ (S : Set E2) (c : Real), H '' slice S c =
      slice (Φ (χ c) '' S) c) :
    H '' (⋃ c ∈ I, slice (L c) c) =
      ⋃ c ∈ I, slice (Φ (χ c) '' L c) c := by
  rw [image_iUnion]
  apply iUnion_congr
  intro c
  rw [image_iUnion]
  apply iUnion_congr
  intro hc
  exact hH (L c) c

theorem planar_diffeomorph_image_ball_frontier
    (D : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) {r : Real} (hr : r ≠ 0) :
    frontier (D '' closedBall (0 : E2) r) = D '' sphere (0 : E2) r := by
  change frontier (D.toHomeomorph '' closedBall (0 : E2) r) =
    D.toHomeomorph '' sphere (0 : E2) r
  rw [← D.toHomeomorph.image_frontier, frontier_closedBall (0 : E2) hr]

end Poincare.Manifold.Schoenflies.Saddle
