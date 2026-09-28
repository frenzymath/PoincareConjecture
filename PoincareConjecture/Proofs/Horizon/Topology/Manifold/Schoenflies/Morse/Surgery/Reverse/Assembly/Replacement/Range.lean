import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Reconstruction

noncomputable section
set_option autoImplicit false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

namespace Reverse

theorem image_filled_sphere_of_image_filled_ball
    (F B L : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hball : F '' (B '' closedBall (0 : E3) 1) = L '' closedBall (0 : E3) 1) :
    F '' (B '' sphere (0 : E3) 1) = L '' sphere (0 : E3) 1 := by
  have hh := congrArg frontier hball
  change frontier (F.toHomeomorph '' (B.toHomeomorph '' closedBall (0 : E3) 1)) =
    frontier (L.toHomeomorph '' closedBall (0 : E3) 1) at hh
  rwa [← F.toHomeomorph.image_frontier, ← B.toHomeomorph.image_frontier,
    ← L.toHomeomorph.image_frontier, frontier_closedBall (0 : E3) one_ne_zero] at hh

end Reverse

namespace SphereSurgeryStep

variable {f : S2 → E3} {v : E3} {c R : Real} (S : SphereSurgeryStep f v c R)

theorem isCompact_prepared_annulus :
    IsCompact ((fun p => S.D (f p)) '' (S.T '' (univ ×ˢ Icc (-S.a) S.a))) := by
  have hs : univ ×ˢ Icc (-S.a) S.a ⊆ S.T.source := by
    rintro ⟨q, t⟩ ⟨_, ht⟩
    rw [S.tube_source]
    exact ⟨mem_univ _, by linarith [ht.1, S.a_lt_quarter_ε, S.a_pos],
      by linarith [ht.2, S.a_lt_quarter_ε, S.a_pos]⟩
  exact ((isCompact_univ.prod isCompact_Icc).image_of_continuousOn
    (S.T.continuousOn.mono hs)).image S.prepared_embedding.contMDiff.continuous

theorem image_prepared_range_of_lower_replacement
    (F L : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hchild : F '' range S.fMinus = L '' sphere (0 : E3) 1)
    (hcap : ∀ y ∈ S.gMinus '' closedBall (0 : E2) 1, F y = y)
    (hannulus : ∀ y ∈ (fun p => S.D (f p)) '' (S.T '' (univ ×ˢ Icc (-S.a) S.a)), F y = y)
    (hother : ∀ y ∈ range S.fPlus, F y = y) :
    F '' range (fun p => S.D (f p)) =
      ((L '' sphere (0 : E3) 1) \ (S.gMinus '' ball (0 : E2) 1)) ∪
        {y : E3 | inner Real v y ∈ Icc (c - S.a) (c + S.a) ∧
          (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ S.A '' sphere 0 1} ∪
      ((fun p => S.D (f p)) '' (S.ePlus '' closedBall 0 1)) := by
  have hcapImage : F '' (S.gMinus '' ball (0 : E2) 1) = S.gMinus '' ball (0 : E2) 1 := by
    calc
      _ = id '' (S.gMinus '' ball (0 : E2) 1) :=
        image_congr (fun y hy => hcap y (image_mono ball_subset_closedBall hy))
      _ = _ := image_id _
  have hotherImage : F '' (range S.fPlus \ (S.gPlus '' ball (0 : E2) 1)) =
      range S.fPlus \ (S.gPlus '' ball (0 : E2) 1) := by
    calc
      _ = id '' (range S.fPlus \ (S.gPlus '' ball (0 : E2) 1)) :=
        image_congr (fun y hy => hother y hy.1)
      _ = _ := image_id _
  have hcylinder := S.cylindrical_slab_eq_tube_image
    (show -S.ε < -S.a by linarith [S.a_lt_quarter_ε, S.a_pos])
    (show S.a < S.ε by linarith [S.a_lt_quarter_ε, S.a_pos])
  rw [← sub_eq_add_neg] at hcylinder
  have hcircleImage : F ''
      {y : E3 | inner Real v y ∈ Icc (c - S.a) (c + S.a) ∧
        (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ S.A '' sphere 0 1} =
      {y : E3 | inner Real v y ∈ Icc (c - S.a) (c + S.a) ∧
        (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ S.A '' sphere 0 1} := by
    rw [hcylinder]
    exact (image_congr hannulus).trans (image_id _)
  rw [S.prepared_range_eq_children_and_cylinder, image_union, image_union,
    image_sdiff (f := (F : E3 → E3)) F.injective, hchild, hcapImage, hcircleImage, hotherImage,
    S.range_minus_open_capPlus]

theorem image_prepared_range_of_upper_replacement
    (F L : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hchild : F '' range S.fPlus = L '' sphere (0 : E3) 1)
    (hcap : ∀ y ∈ S.gPlus '' closedBall (0 : E2) 1, F y = y)
    (hannulus : ∀ y ∈ (fun p => S.D (f p)) '' (S.T '' (univ ×ˢ Icc (-S.a) S.a)), F y = y)
    (hother : ∀ y ∈ range S.fMinus, F y = y) :
    F '' range (fun p => S.D (f p)) =
      ((fun p => S.D (f p)) '' (S.eMinus '' closedBall 0 1)) ∪
        {y : E3 | inner Real v y ∈ Icc (c - S.a) (c + S.a) ∧
          (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ S.A '' sphere 0 1} ∪
      ((L '' sphere (0 : E3) 1) \ (S.gPlus '' ball (0 : E2) 1)) := by
  have hcapImage : F '' (S.gPlus '' ball (0 : E2) 1) = S.gPlus '' ball (0 : E2) 1 := by
    calc
      _ = id '' (S.gPlus '' ball (0 : E2) 1) :=
        image_congr (fun y hy => hcap y (image_mono ball_subset_closedBall hy))
      _ = _ := image_id _
  have hotherImage : F '' (range S.fMinus \ (S.gMinus '' ball (0 : E2) 1)) =
      range S.fMinus \ (S.gMinus '' ball (0 : E2) 1) := by
    calc
      _ = id '' (range S.fMinus \ (S.gMinus '' ball (0 : E2) 1)) :=
        image_congr (fun y hy => hother y hy.1)
      _ = _ := image_id _
  have hcylinder := S.cylindrical_slab_eq_tube_image
    (show -S.ε < -S.a by linarith [S.a_lt_quarter_ε, S.a_pos])
    (show S.a < S.ε by linarith [S.a_lt_quarter_ε, S.a_pos])
  rw [← sub_eq_add_neg] at hcylinder
  have hcircleImage : F ''
      {y : E3 | inner Real v y ∈ Icc (c - S.a) (c + S.a) ∧
        (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ S.A '' sphere 0 1} =
      {y : E3 | inner Real v y ∈ Icc (c - S.a) (c + S.a) ∧
        (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ S.A '' sphere 0 1} := by
    rw [hcylinder]
    exact (image_congr hannulus).trans (image_id _)
  rw [S.prepared_range_eq_children_and_cylinder, image_union, image_union,
    hotherImage, image_sdiff (f := (F : E3 → E3)) F.injective, hchild, hcapImage, hcircleImage,
    S.range_minus_open_capMinus]

end SphereSurgeryStep

end Poincare.Manifold.Schoenflies
