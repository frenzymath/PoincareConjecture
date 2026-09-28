import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneBoundary.Reflection

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

namespace Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap
open Poincare.Geometry.Euclidean
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {v : E3} {g : S2 → E3} {B : Set Real}

def reflectedProtected (D : SphereSurgeryCoreCap v g B) :
    SphereSurgeryCoreCap v (heightReflection D.unit_v ∘ g) (Neg.neg '' B) := {
  D.reflected with
  avoids_protected := by
    intro x hx
    change inner Real v (heightReflection D.unit_v (D.parametrization x)) ∉ Neg.neg '' B
    rw [inner_heightReflection]
    rintro ⟨b, hb, heq⟩
    exact D.avoids_protected x hx (neg_injective heq ▸ hb) }

@[simp] theorem reflectedProtected_chart (D : SphereSurgeryCoreCap v g B) :
    D.reflectedProtected.chart = D.chart := rfl

@[simp] theorem reflectedProtected_center (D : SphereSurgeryCoreCap v g B) :
    D.reflectedProtected.center = -D.center := rfl

@[simp] theorem reflectedProtected_scale (D : SphereSurgeryCoreCap v g B) :
    D.reflectedProtected.scale = -D.scale := rfl

@[simp] theorem reflectedProtected_parametrization (D : SphereSurgeryCoreCap v g B) (x : E2) :
    D.reflectedProtected.parametrization x = heightReflection D.unit_v (D.parametrization x) := rfl

theorem reflectedProtected_height (D : SphereSurgeryCoreCap v g B) (x : E2) :
    inner Real v (D.reflectedProtected.parametrization x) =
      -inner Real v (D.parametrization x) := inner_heightReflection D.unit_v _

theorem reflectedProtected_normalized_height (D : SphereSurgeryCoreCap v g B) (q : S2) :
    (inner Real v ((heightReflection D.unit_v ∘ g) q) - D.reflectedProtected.center) /
      D.reflectedProtected.scale = (inner Real v (g q) - D.center) / D.scale := by
  simp only [comp_apply, inner_heightReflection, reflectedProtected_center,
    reflectedProtected_scale]
  ring

theorem eq_of_data_eq (D E : SphereSurgeryCoreCap v g B)
    (hchart : D.chart = E.chart) (hcenter : D.center = E.center)
    (hscale : D.scale = E.scale) (hplane : D.planeMap = E.planeMap)
    (hparam : D.parametrization = E.parametrization) : D = E := by
  cases D
  cases E
  rw [SphereSurgeryCoreCap.mk.injEq]
  exact ⟨hchart, hcenter, hscale, hplane, hparam⟩

theorem reflectedProtected_injective (hv : ‖v‖ = 1) :
    Injective (show SphereSurgeryCoreCap v g B →
      SphereSurgeryCoreCap v (heightReflection hv ∘ g) (Neg.neg '' B) from
      fun D => D.reflectedProtected) := by
  intro D E h
  apply eq_of_data_eq D E
  · exact congrArg (fun A : SphereSurgeryCoreCap v (heightReflection hv ∘ g)
      (Neg.neg '' B) => A.chart) h
  · exact neg_injective (congrArg SphereSurgeryCoreCap.center h)
  · exact neg_injective (congrArg SphereSurgeryCoreCap.scale h)
  · exact congrArg (fun A : SphereSurgeryCoreCap v (heightReflection hv ∘ g)
      (Neg.neg '' B) => A.planeMap) h
  · funext x
    apply (heightReflection hv).injective
    exact congrArg (fun A => A.parametrization x) h

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap

end

end M38Schoenflies
