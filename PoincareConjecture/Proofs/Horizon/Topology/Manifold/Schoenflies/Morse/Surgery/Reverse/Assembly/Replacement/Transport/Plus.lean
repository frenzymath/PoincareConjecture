import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Transport.ModelStretch
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.RetainedClearance

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SphereSurgeryStep

open Poincare.Geometry.Euclidean
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 -> E3} {v : E3} {c R : Real} (S : SphereSurgeryStep f v c R)

theorem exists_capPlus_transport_across {u : Real} (hu : 0 < u) (hus : u ≤ S.s) :
    ∃ J : Set E3, IsCompact J ∧
      Disjoint J ((fun p => S.D (f p)) '' (S.ePlus '' closedBall 0 1)) ∧
      ∃ H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y ∉ J, H y = y) ∧
        (∀ y ∈ (fun p => S.D (f p)) '' (S.ePlus '' closedBall 0 1), H y = y) ∧
        H '' range S.fPlus =
          (liftPlaneDiffeomorph S.unit_v (c - S.a) (-u) (neg_ne_zero.mpr hu.ne') S.A ''
            boundedCylinderNorthernCap v) ∪
          {y : E3 | inner Real v y ∈ Icc (c - S.a) (c + S.a) ∧
            (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ S.A '' sphere 0 1} ∪
          ((fun p => S.D (f p)) '' (S.ePlus '' closedBall 0 1)) := by
  let P := (fun p => S.D (f p)) '' (S.ePlus '' closedBall 0 1)
  have hP : IsClosed P :=
    (((isCompact_closedBall (0 : E2) 1).image_of_continuousOn
      (S.ePlus.continuousOn.mono S.ePlus_source)).image
      S.prepared_embedding.contMDiff.continuous).isClosed
  have havoid (q : Hemisphere.Plane v) (hq : ‖q‖ ≤ 1)
      (z : Real) (hz : z ∈ Icc (1 / 4 : Real) 2) (t : Real) (ht : t ∈ Icc (0 : Real) 1) :
      (c + S.a + (-S.s) * ((1 - t) * z + t * (2 * S.a / S.s + (u / S.s) * z))) • v +
        (S.A q : E3) ∉ P := by
    let h := c + S.a + (-S.s) * ((1 - t) * z + t * (2 * S.a / S.s + (u / S.s) * z))
    have heq : h = (1 - t) * (c + S.a - S.s * z) + t * (c - S.a - u * z) := by
      dsimp [h]
      field_simp [S.s_pos.ne']
      ring
    have hzero : c + S.a - S.s * z ∈ Ico (c - 2 * S.a) (c + S.a) := by
      constructor
      · nlinarith [mul_le_mul_of_nonneg_left hz.2 S.s_pos.le, S.s_lt_eighth_a, S.a_pos]
      · nlinarith [S.s_pos, hz.1]
    have hone : c - S.a - u * z ∈ Ico (c - 2 * S.a) (c + S.a) := by
      constructor
      · nlinarith [mul_le_mul_of_nonneg_left hz.2 hu.le, S.s_lt_eighth_a, S.a_pos]
      · nlinarith [mul_nonneg hu.le (show 0 ≤ z by linarith [hz.1]), S.a_pos]
    have hbound : h ∈ Ico (c - 2 * S.a) (c + S.a) := by
      rw [heq]
      exact (convex_Ico (c - 2 * S.a) (c + S.a)) hzero hone
        (sub_nonneg.mpr ht.2) ht.1 (by ring)
    have hh : inner Real v (h • v + (S.A q : E3)) = h := by
      simp [inner_add_right, inner_smul_right, S.unit_v,
        Submodule.mem_orthogonal_singleton_iff_inner_right.mp (S.A q).property]
    apply S.not_mem_retainedPlus_of_height_projection
    · rw [hh]
      exact abs_le.mpr ⟨by linarith [hbound.1], by linarith [hbound.2, S.a_pos]⟩
    · have hp : (Hemisphere.Plane v).orthogonalProjectionOnto
          (h • v + (S.A q : E3)) = S.A q := by simp [Hemisphere.Plane]
      rw [hp]
      exact mem_image_of_mem S.A (mem_closedBall_zero_iff.mpr hq)
    · rw [hh]
      exact hbound.2
  obtain ⟨J, hJ, hJP, H, hfix, hfixP, hcap⟩ := Reverse.exists_model_cap_stretch S.unit_v
    (c + S.a) (-S.s) (neg_ne_zero.mpr S.s_pos.ne') S.A
    (d := 2 * S.a / S.s) (k := u / S.s)
    (div_nonneg (by linarith [S.a_pos]) S.s_pos.le) (div_pos hu S.s_pos) P hP havoid
  have hb : c + S.a + -S.s * (2 * S.a / S.s) = c - S.a := by field_simp [S.s_pos.ne']; ring
  have hs : -S.s * (u / S.s) = -u := by field_simp [S.s_pos.ne']
  have hcyl : {y : E3 | (inner Real v y - (c + S.a)) / (-S.s) ∈ Icc 0 (2 * S.a / S.s) ∧
      (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ S.A '' sphere 0 1} =
      {y : E3 | inner Real v y ∈ Icc (c - S.a) (c + S.a) ∧
        (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ S.A '' sphere 0 1} := by
    ext y
    have hn : (inner Real v y - (c + S.a)) / (-S.s) = (c + S.a - inner Real v y) / S.s := by ring
    simp only [mem_ofPred_eq, hn]
    apply and_congr_left
    intro _
    constructor
    · intro h
      have h0 := (le_div_iff₀ S.s_pos).mp h.1
      have h1 := (div_le_div_iff_of_pos_right S.s_pos).mp h.2
      exact ⟨by linarith, by linarith⟩
    · intro h
      exact ⟨(le_div_iff₀ S.s_pos).mpr (by linarith [h.2]),
        (div_le_div_iff_of_pos_right S.s_pos).mpr (by linarith [h.1])⟩
  simp only [hb, hs, hcyl] at hcap
  have hg : S.gPlus '' closedBall (0 : E2) 1 =
      liftPlaneDiffeomorph S.unit_v (c + S.a) (-S.s) (neg_ne_zero.mpr S.s_pos.ne') S.A ''
        boundedCylinderNorthernCap v := S.gPlus_range
  have hret : H '' P = P := by
    calc
      H '' P = id '' P := image_congr hfixP
      _ = P := image_id _
  refine ⟨J, hJ, hJP, H, hfix, hfixP, ?_⟩
  rw [S.fPlus_range, image_union, hg, hcap]
  exact congrArg (fun T : Set E3 => _ ∪ T) hret

end Poincare.Manifold.Schoenflies.SphereSurgeryStep
