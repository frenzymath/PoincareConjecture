import PoincareConjecture.Proofs.M38.ProjectiveFramedPolar
import PoincareConjecture.Proofs.M38.TwoBallAffineNormalization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

open Poincare.Topology

variable (L : StandardCapSpace ≃L[ℝ] StandardCapSpace)
  (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))

theorem projectivePolar_zero_ne_affine (z : UnitTwoSphere) (x : StandardCapSpace) :
    projectivePolarMap.{u} R (z, 0) ≠ projectiveAffineMap R x := by
  intro h
  have hzero : (spherePolarMap (z, 0)).val 0 = 0 := by
    change ‖spherePolarVector (z, 0)‖⁻¹ * 0 = 0
    exact mul_zero _
  have hx := sphereAffineMap_positive x
  rcases (projectiveOrthogonal_fibers R _ _).mp h with he | he
  · have hh := congrArg (fun a : UnitThreeSphere => a.val 0) he
    rw [hzero] at hh
    linarith
  · have hh := congrArg (fun a : UnitThreeSphere => a.val 0) he
    change (spherePolarMap (z, 0)).val 0 = -(sphereAffineMap x).val 0 at hh
    rw [hzero] at hh
    linarith

theorem projectiveFramedPolar_affine_of_ne_zero (z : UnitTwoSphere) {t : ℝ} (ht : t ≠ 0) :
    projectiveFramedPolarMap.{u} L R (z, t) = projectiveAffineMap R (L (t⁻¹ • z.val)) := by
  rcases lt_or_gt_of_ne ht with ht | ht
  · have he : projectiveFramedPolarMap.{u} L R (z, t) =
        projectiveFramedPolarMap L R (-z, -t) :=
      (projectiveFramedPolar_fibers L R _ _).mpr (Or.inr (by simp))
    rw [he, projectiveFramedPolar_affine L R (-z) (neg_pos.mpr ht)]
    change projectiveAffineMap R (L ((-t)⁻¹ • -z.val)) = _
    rw [inv_neg, neg_smul, smul_neg, neg_neg]
  · exact projectiveFramedPolar_affine L R z ht

theorem projectiveFramedPolar_mem_affine_ball_iff (p : RoundCylinderSpace) :
    projectiveFramedPolarMap.{u} L R p ∈
        (fun x => projectiveAffineMap R (L x)) '' Metric.closedBall 0 1 ↔
      1 ≤ |p.2| := by
  constructor
  · rintro ⟨x, hx, he⟩
    have ht : p.2 ≠ 0 := by
      intro ht
      have hp : p = (p.1, (0 : ℝ)) := Prod.ext rfl ht
      rw [hp] at he
      change projectiveAffineMap R (L x) =
        projectivePolarMap R (linearSphereDiffeomorph L p.1, 0 / ‖L p.1.val‖) at he
      rw [zero_div] at he
      exact projectivePolar_zero_ne_affine R _ _ he.symm
    have hformula := projectiveFramedPolar_affine_of_ne_zero.{u} L R p.1 ht
    change projectiveFramedPolarMap L R p = _ at hformula
    have heq : x = p.2⁻¹ • p.1.val :=
      L.injective ((projectiveAffineMap_injective R) (he.trans hformula))
    have hn : |p.2|⁻¹ ≤ 1 := by
      rw [heq] at hx
      simpa only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_inv, norm_eq_of_mem_sphere, mul_one] using hx
    exact (inv_le_one₀ (abs_pos.mpr ht)).mp hn
  · intro ht
    have hpos : 0 < |p.2| := zero_lt_one.trans_le ht
    have hne : p.2 ≠ 0 := abs_pos.mp hpos
    refine ⟨p.2⁻¹ • p.1.val, ?_, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_inv, norm_eq_of_mem_sphere, mul_one] using (inv_le_one₀ hpos).mpr ht
    · exact (projectiveFramedPolar_affine_of_ne_zero L R p.1 hne).symm

theorem exists_projectiveBall_cylindrical_cover (B : SurgeryBallEmbedding projectiveCarrier.{u}) :
    ∃ q : RoundCylinderSpace → projectiveCarrier.{u}.carrier,
      IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ q ∧
      (∀ x y, q x = q y ↔ x = y ∨ x = (-y.1, -y.2)) ∧
      range q = {B.map 0}ᶜ ∧
      (∀ p, q p ∈ B.closedBall ↔ 1 ≤ |p.2|) ∧
      q '' (univ ×ˢ Ioo (-1 : ℝ) 1) = B.closedBallᶜ ∧
      ∀ (z : UnitTwoSphere) (r : ℝ), 0 < r → r ≤ 5 / 4 → q (z, r⁻¹) = B.map (r • z.val) := by
  obtain ⟨R, C, hC, hcenter⟩ := exists_projectiveAffineReferenceBall (B.map 0)
  obtain ⟨e, L, b, _, hb, _, he, _, _⟩ := exists_surgeryBallAffineNormalizationCompact B C
    ⟨0, by simp, hcenter⟩
  have hc0 : C.inverse (B.map 0) = 0 := by
    rw [← hcenter]
    exact C.left_inverse (by simp)
  let S : StandardCapSpace ≃L[ℝ] StandardCapSpace :=
    ((LinearEquiv.smulOfNeZero ℝ StandardCapSpace b hb.ne').toContinuousLinearEquiv).trans L
  have hES (x : StandardCapSpace) (hx : ‖x‖ ≤ 5 / 4) :
      e (B.map x) = projectiveAffineMap R (S x) := by
    rw [he x hx, hc0, zero_add, hC]
    rfl
  have he0 : e (B.map 0) = projectiveAffineMap R 0 := by
    simpa only [map_zero] using hES 0 (by norm_num)
  let f := projectiveFramedPolarMap.{u} S R
  let q := e.symm ∘ f
  have hq : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ q := fun p =>
    (projectiveFramedPolar_localDiffeomorph S R p).comp
      (𝓡 3) projectiveCarrier.carrier (e.symm.isLocalDiffeomorph _)
  have hball : e '' B.closedBall =
      (fun x => projectiveAffineMap R (S x)) '' Metric.closedBall 0 1 := by
    rw [SurgeryBallEmbedding.closedBall, ← image_comp]
    apply image_congr
    intro x hx
    exact hES x (by have := Metric.mem_closedBall.mp hx; rw [dist_zero_right] at this; linarith)
  have hmem (p : RoundCylinderSpace) : q p ∈ B.closedBall ↔ 1 ≤ |p.2| := by
    have h₁ : q p ∈ B.closedBall ↔ f p ∈ e '' B.closedBall := by
      constructor
      · intro hp
        exact ⟨q p, hp, e.apply_symm_apply (f p)⟩
      · rintro ⟨x, hx, heq⟩
        have hqx : q p = x := (congrArg e.symm heq).symm.trans (e.symm_apply_apply x)
        exact hqx.symm ▸ hx
    rw [h₁, hball]
    exact projectiveFramedPolar_mem_affine_ball_iff S R p
  have hrange : range q = {B.map 0}ᶜ := by
    ext y
    constructor
    · rintro ⟨p, rfl⟩ hy
      have hp : f p ∈ ({projectiveAffineMap R 0}ᶜ : Set projectiveCarrier.{u}.carrier) :=
        (projectiveFramedPolar_range S R).subset (mem_range_self p)
      apply hp
      have hh := congrArg e hy
      change e (e.symm (f p)) = e (B.map 0) at hh
      rwa [e.apply_symm_apply, he0] at hh
    · intro hy
      have hey : e y ≠ projectiveAffineMap R 0 := by
        rw [← he0]
        exact fun h => hy (e.injective h)
      obtain ⟨p, hp⟩ := (projectiveFramedPolar_range S R).superset hey
      exact ⟨p, (congrArg e.symm hp).trans (e.symm_apply_apply y)⟩
  refine ⟨q, hq, ?_, hrange, hmem, ?_, ?_⟩
  · intro x y
    have hinj : Function.Injective (e.symm : projectiveCarrier.carrier → projectiveCarrier.carrier) :=
      e.symm.injective
    exact hinj.eq_iff.trans (projectiveFramedPolar_fibers S R x y)
  · apply subset_antisymm
    · rintro _ ⟨p, hp, rfl⟩ hB
      exact (not_le.mpr (abs_lt.mpr hp.2)) ((hmem p).mp hB)
    · intro y hy
      have hy0 : y ≠ B.map 0 := by
        intro hy0
        apply hy
        rw [hy0]
        exact mem_image_of_mem B.map (by simp)
      obtain ⟨p, rfl⟩ := hrange.superset hy0
      exact ⟨p, ⟨mem_univ _, abs_lt.mp (lt_of_not_ge (fun hp => hy ((hmem p).mpr hp)))⟩, rfl⟩
  · intro z r hr hrmax
    change e.symm (projectiveFramedPolarMap S R (z, r⁻¹)) = B.map (r • z.val)
    rw [projectiveFramedPolar_affine S R z (inv_pos.mpr hr), inv_inv, ← hES]
    · exact e.symm_apply_apply _
    · simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_eq_of_mem_sphere, mul_one] using hrmax

end PoincareConjecture.M38
