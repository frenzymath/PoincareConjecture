import PoincareConjecture.Proofs.M76.Mathlib.FramePlaneCoordinates
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap










set_option autoImplicit false

open Set

namespace ContinuousLinearMap

variable {E F T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup T] [NormedSpace ℝ T]



def tangentCylinderProjection (B : E →L[ℝ] F) (A : E →L[ℝ] T) : (E × T) →L[ℝ] (F × T) :=
  (B.comp (fst ℝ E T)).prod (snd ℝ E T + A.comp (fst ℝ E T))



theorem tangentCylinderProjection_apply (B : E →L[ℝ] F) (A : E →L[ℝ] T) (x : E) (t : T) :
    tangentCylinderProjection B A (x, t) = (B x, t + A x) := rfl




theorem injOn_tangentCylinderProjection_iff (B : E →L[ℝ] F) (A : E →L[ℝ] T) (S : Set E) :
    InjOn (tangentCylinderProjection B A) (S ×ˢ (univ : Set T)) ↔ InjOn B S := by
  constructor
  · intro h x hx y hy he
    have hxy := h (x₁ := (x, -A x)) (x₂ := (y, -A y)) ⟨hx, mem_univ _⟩
      ⟨hy, mem_univ _⟩ (by simp only [tangentCylinderProjection_apply, neg_add_cancel, he])
    exact congrArg Prod.fst hxy
  · intro h x hx y hy he
    have hn : x.1 = y.1 := h hx.1 hy.1 (congrArg Prod.fst he)
    apply Prod.ext hn
    have ht := congrArg Prod.snd he
    change x.2 + A x.1 = y.2 + A y.1 at ht
    rw [hn] at ht
    exact add_right_cancel ht




theorem rightInverse_tangentCylinderProjection_iff (J : F →L[ℝ] E)
    (B : E →L[ℝ] F) (A : E →L[ℝ] T) :
    Function.RightInverse (J.prodMap (ContinuousLinearMap.id ℝ T)) (tangentCylinderProjection B A) ↔
      Function.RightInverse J B ∧ A.comp J = 0 := by
  constructor
  · intro h
    refine ⟨fun f => congrArg Prod.fst (h (f, 0)), ?_⟩
    apply ContinuousLinearMap.ext
    intro f
    have ht := congrArg Prod.snd (h (f, 0))
    change (0 : T) + A (J f) = 0 at ht
    change A (J f) = 0
    simpa only [zero_add] using ht
  · rintro ⟨hB, hA⟩ ⟨f, t⟩
    change (B (J f), t + A (J f)) = (f, t)
    have hz : A (J f) = 0 := congrArg (fun L : F →L[ℝ] T => L f) hA
    rw [hB f, hz, add_zero]




theorem eq_tangentCylinderProjection_of_fixed_tangent (Q : (E × T) →L[ℝ] (F × T))
    (hT : ∀ t : T, Q (0, t) = (0, t)) :
    Q = tangentCylinderProjection ((fst ℝ F T).comp (Q.comp (inl ℝ E T)))
      ((snd ℝ F T).comp (Q.comp (inl ℝ E T))) := by
  apply ContinuousLinearMap.ext
  rintro ⟨x, t⟩
  change Q (x, t) = ((Q (x, 0)).1, t + (Q (x, 0)).2)
  have he : (x, t) = (x, (0 : T)) + (0, t) := by simp
  rw [he, map_add, hT]
  ext <;> simp [add_comm]




theorem fixed_tangent_of_rightInverse_productFrame (J : F →L[ℝ] E)
    (Q : (E × T) →L[ℝ] (F × T))
    (hQ : Function.RightInverse (J.prodMap (ContinuousLinearMap.id ℝ T)) Q) (t : T) :
    Q (0, t) = (0, t) := by
  have he := hQ (0, t)
  change Q (J 0, t) = (0, t) at he
  simpa only [map_zero] using he

end ContinuousLinearMap
