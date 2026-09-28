import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Correction.CapBelt

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

private theorem range_diff_open_cap
    (f f' : S2 → E3) (g : E2 → E3) (d : OpenPartialHomeomorph E2 S2)
    (K : Set S2) (hfi : Injective f')
    (hopen : d '' ball (0 : E2) 1 = Kᶜ)
    (hpatch : ∀ x ∈ closedBall (0 : E2) 1, f' (d x) = g x)
    (hretained : ∀ p ∈ K, f' p = f p) :
    range f' \ (g '' ball (0 : E2) 1) = f '' K := by
  have hcap : g '' ball (0 : E2) 1 = f' '' Kᶜ := by
    rw [← hopen, ← image_comp]
    exact image_congr fun x hx => (hpatch x (ball_subset_closedBall hx)).symm
  rw [hcap, ← image_univ, ← image_sdiff hfi,
    show univ \ Kᶜ = K by ext; simp]
  exact image_congr hretained

namespace SphereSurgeryStep

variable {f : S2 → E3} {v : E3} {c R : Real} (S : SphereSurgeryStep f v c R)

theorem range_minus_open_capMinus :
    range S.fMinus \ (S.gMinus '' ball (0 : E2) 1) =
      (fun p => S.D (f p)) '' (S.eMinus '' closedBall 0 1) :=
  range_diff_open_cap _ _ _ _ _ S.fMinus_embedding.isEmbedding.injective S.dMinus_open
    S.capMinus_eq S.retainedMinus_eq

theorem range_minus_open_capPlus :
    range S.fPlus \ (S.gPlus '' ball (0 : E2) 1) =
      (fun p => S.D (f p)) '' (S.ePlus '' closedBall 0 1) :=
  range_diff_open_cap _ _ _ _ _ S.fPlus_embedding.isEmbedding.injective S.dPlus_open
    S.capPlus_eq S.retainedPlus_eq

theorem prepared_range_eq_children_and_cylinder :
    range (fun p => S.D (f p)) =
      (range S.fMinus \ (S.gMinus '' ball (0 : E2) 1)) ∪
        {y : E3 | inner Real v y ∈ Icc (c - S.a) (c + S.a) ∧
          (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ S.A '' sphere 0 1} ∪
      (range S.fPlus \ (S.gPlus '' ball (0 : E2) 1)) := by
  rw [S.range_minus_open_capMinus, S.range_minus_open_capPlus]
  have hmiddle := S.cylindrical_slab_eq_tube_image
    (show -S.ε < -S.a by linarith [S.a_lt_quarter_ε, S.a_pos])
    (show S.a < S.ε by linarith [S.a_lt_quarter_ε, S.a_pos])
  rw [← sub_eq_add_neg] at hmiddle
  rw [hmiddle, ← image_union, ← image_union, S.disk_slab_cover, image_univ]

theorem prepared_range_eq_filled_boundaries_and_cylinder
    (BMinus BPlus : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hMinus : BMinus '' sphere (0 : E3) 1 = range S.fMinus)
    (hPlus : BPlus '' sphere (0 : E3) 1 = range S.fPlus) :
    range (fun p => S.D (f p)) =
      ((BMinus '' sphere (0 : E3) 1) \ (S.gMinus '' ball (0 : E2) 1)) ∪
        {y : E3 | inner Real v y ∈ Icc (c - S.a) (c + S.a) ∧
          (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ S.A '' sphere 0 1} ∪
      ((BPlus '' sphere (0 : E3) 1) \ (S.gPlus '' ball (0 : E2) 1)) := by
  rw [hMinus, hPlus]
  exact S.prepared_range_eq_children_and_cylinder

theorem child_fillings_disjoint_or_nested
    (BMinus BPlus : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hMinus : BMinus '' sphere (0 : E3) 1 = range S.fMinus)
    (hPlus : BPlus '' sphere (0 : E3) 1 = range S.fPlus) :
    Disjoint (BMinus '' closedBall (0 : E3) 1) (BPlus '' closedBall (0 : E3) 1) ∨
      BMinus '' closedBall (0 : E3) 1 ⊆ BPlus '' ball (0 : E3) 1 ∨
      BPlus '' closedBall (0 : E3) 1 ⊆ BMinus '' ball (0 : E3) 1 := by
  apply BMinus.toHomeomorph.disjoint_or_nested_image_closedBall BPlus.toHomeomorph
  · rw [← Module.finrank_eq_rank]
    norm_num [E3, finrank_euclideanSpace]
  · change Disjoint (BMinus '' sphere (0 : E3) 1) (BPlus '' sphere (0 : E3) 1)
    rw [hMinus, hPlus]
    exact S.children_disjoint

end SphereSurgeryStep

end Poincare.Manifold.Schoenflies

end

end M38Schoenflies
