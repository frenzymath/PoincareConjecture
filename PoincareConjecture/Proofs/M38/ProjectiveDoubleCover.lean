import PoincareConjecture.Proofs.M38.ProjectiveDoubleFibers
import PoincareConjecture.Proofs.M38.CylinderDihedralCover











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

attribute [local instance] cylinderDihedralAction



theorem exists_projectiveDouble_cylinder_cover
    (A : GeneralizedSliceCarrier.{u}) (C : SmoothProjectiveDoubleModel A.carrier) :
    ∃ q : RoundCylinderSpace → A.carrier,
      IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ q ∧
      Function.Surjective q ∧ range q = univ ∧
      (∀ x y, q x = q y ↔
        ∃ n : ℤ, x = cylinderIntegerTranslation n y ∨ x = cylinderIntegerReflection n y) ∧
      IsQuotientCoveringMap q (DihedralGroup 0) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ (z : UnitTwoSphere) (s : ℝ), |s| < r →
          q (z, (1 + s / 2) / 4) = C.collar (z, s) := by
  obtain ⟨r, f, g, hr, hrs, hfl, hgl, hfi, hgi, hfr, hgr, hff, hgf, hf, hg⟩ :=
    exists_projectiveDouble_side_covers A C
  let q₄ := projectiveDoubleProjection4 C f g
  have hq₄ := projectiveDoubleProjection4_localDiffeomorph C f g
    (projectiveDoubleCycle_localDiffeomorph C f g hr hrs hf hg hfl hgl hfr hgr)
  let D := cylinderAffineChange 4 0 (by norm_num)
  let q := q₄ ∘ D
  have hq : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ q := fun p =>
    (D.isLocalDiffeomorph p).comp (𝓡 3) A.carrier (hq₄ _)
  have hsurj : Function.Surjective q :=
    (projectiveDoubleProjection4_surjective C f g hfi hgi).comp D.surjective
  have hdeck (x y : RoundCylinderSpace) : q x = q y ↔
      ∃ n : ℤ, x = cylinderIntegerTranslation n y ∨ x = cylinderIntegerReflection n y := by
    change q₄ (D x) = q₄ (D y) ↔ _
    rw [projectiveDoubleProjection4_fibers C f g hfi hgi hfr hgr hff hgf]
    constructor
    · rintro ⟨n, h | h⟩
      · refine ⟨n, Or.inl ?_⟩
        apply Prod.ext
        · exact h.1
        · change x.2 = y.2 + (n : ℝ)
          have ht := h.2
          change 4 * x.2 + 0 = (4 * y.2 + 0) + (n : ℝ) * 4 at ht
          linarith
      · refine ⟨n, Or.inr ?_⟩
        apply Prod.ext
        · exact h.1
        · change x.2 = (n : ℝ) - y.2
          have ht := h.2
          change 4 * x.2 + 0 = (n : ℝ) * 4 - (4 * y.2 + 0) at ht
          linarith
    · rintro ⟨n, h | h⟩
      · subst x
        refine ⟨n, Or.inl ⟨rfl, ?_⟩⟩
        change 4 * (y.2 + (n : ℝ)) + 0 = (4 * y.2 + 0) + (n : ℝ) * 4
        ring
      · subst x
        refine ⟨n, Or.inr ⟨rfl, ?_⟩⟩
        change 4 * ((n : ℝ) - y.2) + 0 = (n : ℝ) * 4 - (4 * y.2 + 0)
        ring
  refine ⟨q, hq, hsurj, hsurj.range_eq, hdeck,
    cylinderDihedral_isQuotientCoveringMap q hq hsurj hdeck, r, hr, ?_⟩
  intro z s hs
  have hb := abs_lt.mp hs
  change projectiveDoubleProjection4 C f g (z, 4 * ((1 + s / 2) / 4) + 0) = _
  rw [show 4 * ((1 + s / 2) / 4) + 0 = 1 + s / 2 by ring]
  rw [projectiveDoubleProjection4_fundamental C f g
    ⟨by linarith, by linarith⟩,
    projectiveDoubleCycle_first_collar C f g hrs hf hg z ⟨by linarith, by linarith⟩]
  congr 2
  ring

end PoincareConjecture.M38
