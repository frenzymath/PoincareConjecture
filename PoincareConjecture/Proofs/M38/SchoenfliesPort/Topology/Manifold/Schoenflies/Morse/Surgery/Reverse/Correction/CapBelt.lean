import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.StepLens
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CappedCylinder.Belt







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
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

private theorem mem_northern_model_iff_of_height_belt
    {v : E3} (hv : ‖v‖ = 1) (y : E3)
    (hy : inner Real v y ∈ Icc (0 : Real) (1 / 4)) :
    y ∈ (fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
        {p : S2 | 0 ≤ inner Real v (p : E3)} ↔
      ‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ = 1 := by
  have habs : |inner Real v y| ≤ 1 / 4 := by
    rw [abs_of_nonneg hy.1]
    exact hy.2
  constructor
  · rintro ⟨p, _, rfl⟩
    exact norm_boundedCylinder_projection_eq_one_of_height_belt v hv p habs
  · intro hnorm
    obtain ⟨p, hpy⟩ := (mem_boundedCylinder_sphere_iff_of_height_belt v hv y habs).mpr hnorm
    refine ⟨p, ?_, hpy⟩
    have hp := hy.1
    rw [← hpy, inner_smul_right] at hp
    exact nonneg_of_mul_nonneg_right hp (boundedCylinderRadius_pos v p)



theorem mem_transported_cap_iff_of_normalized_height_mem_Icc
    {v : E3} (hv : ‖v‖ = 1) (c s : Real) (hs : s ≠ 0)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (g : E2 → E3)
    (hcore : g '' closedBall (0 : E2) 1 =
      Poincare.Geometry.Euclidean.liftPlaneDiffeomorph hv c s hs A ''
        ((fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
          {p : S2 | 0 ≤ inner Real v (p : E3)}))
    (y : E3) (hy : (inner Real v y - c) / s ∈ Icc (0 : Real) (1 / 4)) :
    y ∈ g '' closedBall (0 : E2) 1 ↔
      (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' sphere 0 1 := by
  let T := Poincare.Geometry.Euclidean.liftPlaneDiffeomorph hv c s hs A
  obtain ⟨z, rfl⟩ := T.surjective y
  change (inner Real v (T z) - c) / s ∈ Icc (0 : Real) (1 / 4) at hy
  have hheight : (inner Real v (T z) - c) / s = inner Real v z := by
    rw [Poincare.Geometry.Euclidean.inner_liftPlaneDiffeomorph]
    field_simp
    ring
  rw [hheight] at hy
  rw [hcore]
  change T z ∈ T '' _ ↔ (Hemisphere.Plane v).orthogonalProjectionOnto (T z) ∈ A '' sphere 0 1
  have hTi : Injective (T : E3 → E3) := T.injective
  have hAi : Injective (A : Hemisphere.Plane v → Hemisphere.Plane v) := A.injective
  rw [hTi.mem_set_image,
    Poincare.Geometry.Euclidean.projection_liftPlaneDiffeomorph,
    hAi.mem_set_image, mem_sphere_zero_iff_norm]
  exact mem_northern_model_iff_of_height_belt hv z hy

namespace SphereSurgeryStep

variable {f : S2 → E3} {v : E3} {c R : Real} (S : SphereSurgeryStep f v c R)


theorem capMinus_height_ge_cut {y : E3} (hy : y ∈ S.gMinus '' closedBall (0 : E2) 1) :
    c - S.a ≤ inner Real v y := by
  obtain ⟨_, ⟨p, hp, rfl⟩, rfl⟩ := S.gMinus_range ▸ hy
  rw [Poincare.Geometry.Euclidean.inner_liftPlaneDiffeomorph, inner_smul_right]
  exact le_add_of_nonneg_right (mul_nonneg S.s_pos.le
    (mul_nonneg (boundedCylinderRadius_pos v p).le hp))


theorem capPlus_height_le_cut {y : E3} (hy : y ∈ S.gPlus '' closedBall (0 : E2) 1) :
    inner Real v y ≤ c + S.a := by
  obtain ⟨_, ⟨p, hp, rfl⟩, rfl⟩ := S.gPlus_range ▸ hy
  rw [Poincare.Geometry.Euclidean.inner_liftPlaneDiffeomorph, inner_smul_right]
  exact add_le_of_nonpos_right (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr S.s_pos.le)
    (mul_nonneg (boundedCylinderRadius_pos v p).le hp))



theorem cylindrical_slab_eq_tube_image
    {l u : Real} (hl : -S.ε < l) (hu : u < S.ε) :
    {y : E3 | inner Real v y ∈ Icc (c + l) (c + u) ∧
      (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ S.A '' sphere 0 1} =
      (fun p => S.D (f p)) '' (S.T '' (univ ×ˢ Icc l u)) := by
  ext y
  constructor
  · rintro ⟨hyheight, hyproj⟩
    rw [S.circle_image] at hyproj
    obtain ⟨q, hqy⟩ := hyproj
    let t := inner Real v y - c
    have ht : t ∈ Icc l u := ⟨by dsimp [t]; linarith [hyheight.1],
      by dsimp [t]; linarith [hyheight.2]⟩
    refine ⟨S.T (q, t), ⟨(q, t), ⟨mem_univ q, ht⟩, rfl⟩, ?_⟩
    dsimp only
    rw [S.cylinder q t ⟨hl.trans_le ht.1, ht.2.trans_lt hu⟩]
    have heq := (Poincare.Geometry.Euclidean.heightCoordinates S.unit_v).apply_symm_apply y
    change inner Real v y • v +
      ((Hemisphere.Plane v).orthogonalProjectionOnto y : E3) = y at heq
    rw [← hqy] at heq
    rw [show c + t = inner Real v y by dsimp [t]; ring]
    exact heq
  · rintro ⟨_, ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩, rfl⟩
    dsimp only
    rw [S.cylinder q t ⟨hl.trans_le ht.1, ht.2.trans_lt hu⟩]
    have hheight : inner Real v ((c + t) • v + (S.γ q : E3)) = c + t := by
      simp [inner_add_right, inner_smul_right, S.unit_v,
        Submodule.mem_orthogonal_singleton_iff_inner_right.mp (S.γ q).property]
    refine ⟨?_, ?_⟩
    · rw [hheight]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · rw [S.circle_image]
      simp [Hemisphere.Plane,
        Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero]



theorem capMinus_belt_eq_original_annulus :
    (S.gMinus '' closedBall (0 : E2) 1) ∩
      {y : E3 | inner Real v y ∈ Icc (c - S.a) (c - S.a + S.s / 4)} =
      (fun p => S.D (f p)) '' (S.T '' (univ ×ˢ Icc (-S.a) (-S.a + S.s / 4))) := by
  rw [← S.cylindrical_slab_eq_tube_image
    (show -S.ε < -S.a by linarith [S.a_lt_quarter_ε, S.a_pos])
    (show -S.a + S.s / 4 < S.ε by
      linarith [S.s_lt_eighth_a, S.a_lt_quarter_ε, S.a_pos])]
  ext y
  have heq (hy : inner Real v y ∈ Icc (c - S.a) (c - S.a + S.s / 4)) :=
    mem_transported_cap_iff_of_normalized_height_mem_Icc S.unit_v (c - S.a) S.s
      S.s_pos.ne' S.A S.gMinus S.gMinus_range y
      (show (inner Real v y - (c - S.a)) / S.s ∈ Icc (0 : Real) (1 / 4) from
        ⟨div_nonneg (by linarith [hy.1]) S.s_pos.le,
          (div_le_iff₀ S.s_pos).mpr (by linarith [hy.2])⟩)
  have hends : c + -S.a = c - S.a ∧
      c + (-S.a + S.s / 4) = c - S.a + S.s / 4 := by constructor <;> ring
  simp only [mem_inter_iff, mem_ofPred_eq, hends.1, hends.2]
  exact ⟨fun hy => ⟨hy.2, (heq hy.2).mp hy.1⟩,
    fun hy => ⟨(heq hy.1).mpr hy.2, hy.1⟩⟩



theorem capPlus_belt_eq_original_annulus :
    (S.gPlus '' closedBall (0 : E2) 1) ∩
      {y : E3 | inner Real v y ∈ Icc (c + S.a - S.s / 4) (c + S.a)} =
      (fun p => S.D (f p)) '' (S.T '' (univ ×ˢ Icc (S.a - S.s / 4) S.a)) := by
  rw [← S.cylindrical_slab_eq_tube_image
    (show -S.ε < S.a - S.s / 4 by
      linarith [S.s_lt_eighth_a, S.a_lt_quarter_ε, S.a_pos])
    (show S.a < S.ε by linarith [S.a_lt_quarter_ε, S.a_pos])]
  ext y
  have hquot : (inner Real v y - (c + S.a)) / (-S.s) =
      (c + S.a - inner Real v y) / S.s := by ring
  have heq (hy : inner Real v y ∈ Icc (c + S.a - S.s / 4) (c + S.a)) :=
    mem_transported_cap_iff_of_normalized_height_mem_Icc S.unit_v (c + S.a) (-S.s)
      (neg_ne_zero.mpr S.s_pos.ne') S.A S.gPlus S.gPlus_range y
      (show (inner Real v y - (c + S.a)) / (-S.s) ∈ Icc (0 : Real) (1 / 4) by
        rw [hquot]
        exact ⟨div_nonneg (by linarith [hy.2]) S.s_pos.le,
          (div_le_iff₀ S.s_pos).mpr (by linarith [hy.1])⟩)
  have hend : c + (S.a - S.s / 4) = c + S.a - S.s / 4 := by ring
  simp only [mem_inter_iff, mem_ofPred_eq, hend]
  exact ⟨fun hy => ⟨hy.2, (heq hy.2).mp hy.1⟩,
    fun hy => ⟨(heq hy.1).mpr hy.2, hy.1⟩⟩



theorem capMinus_mem_prepared_of_height_near_cut {y : E3}
    (hy : y ∈ S.gMinus '' closedBall (0 : E2) 1)
    (hheight : |inner Real v y - (c - S.a)| ≤ S.s / 4) :
    y ∈ range (fun p => S.D (f p)) := by
  have hmem : y ∈ (S.gMinus '' closedBall (0 : E2) 1) ∩
      {y : E3 | inner Real v y ∈ Icc (c - S.a) (c - S.a + S.s / 4)} :=
    ⟨hy, S.capMinus_height_ge_cut hy, by linarith [(abs_le.mp hheight).2]⟩
  rw [S.capMinus_belt_eq_original_annulus] at hmem
  exact image_subset_range _ _ hmem


theorem capPlus_mem_prepared_of_height_near_cut {y : E3}
    (hy : y ∈ S.gPlus '' closedBall (0 : E2) 1)
    (hheight : |inner Real v y - (c + S.a)| ≤ S.s / 4) :
    y ∈ range (fun p => S.D (f p)) := by
  have hmem : y ∈ (S.gPlus '' closedBall (0 : E2) 1) ∩
      {y : E3 | inner Real v y ∈ Icc (c + S.a - S.s / 4) (c + S.a)} :=
    ⟨hy, by linarith [(abs_le.mp hheight).1], S.capPlus_height_le_cut hy⟩
  rw [S.capPlus_belt_eq_original_annulus] at hmem
  exact image_subset_range _ _ hmem

end SphereSurgeryStep

end Poincare.Manifold.Schoenflies

end

end M38Schoenflies
