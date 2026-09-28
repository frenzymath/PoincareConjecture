import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Collar.Differential
import Mathlib.Analysis.InnerProductSpace.TwoDim

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := Metric.sphere (0 : E2) 1

private instance : Fact (Module.finrank Real E2 = 2) := ⟨by simp⟩
private instance : Fact (Module.finrank Real E2 = 1 + 1) := ⟨by simp⟩

private def circleOrientation : Orientation Real E2 (Fin 2) :=
  (EuclideanSpace.basisFun (Fin 2) Real).toBasis.orientation

def circleQuarterTurn : E2 ≃ₗᵢ[Real] E2 := circleOrientation.rightAngleRotation

theorem inner_circleQuarterTurn_self (p : E2) :
    inner Real (circleQuarterTurn p) p = 0 :=
  circleOrientation.inner_rightAngleRotation_self p

theorem inner_self_circleQuarterTurn (p : E2) :
    inner Real p (circleQuarterTurn p) = 0 := by
  rw [real_inner_comm, inner_circleQuarterTurn_self]

private theorem eq_smul_circleQuarterTurn_of_inner_eq_zero
    (p v : E2) (hp : inner Real p p = 1) (hv : inner Real p v = 0) :
    ∃ a : Real, v = a • circleQuarterTurn p := by
  have hp0 : p ≠ 0 := by
    intro h
    simp [h] at hp
  let b := circleOrientation.basisRightAngleRotation p hp0
  have hrepr : v = b.repr v 0 • p + b.repr v 1 • circleQuarterTurn p := by
    simpa [b, Fin.sum_univ_two, circleQuarterTurn] using (b.sum_repr v).symm
  have hz : b.repr v 0 = 0 := by
    have h := congrArg (inner Real p) hrepr
    simpa only [hv, inner_add_right, inner_smul_right, hp,
      inner_self_circleQuarterTurn, mul_one, mul_zero, add_zero] using h.symm
  exact ⟨b.repr v 1, by simpa [hz] using hrepr⟩

def circleNormal (A : E2 →L[Real] E2) (p : E2) : E2 :=
  circleQuarterTurn (A (circleQuarterTurn p))

theorem inner_circleNormal_apply_eq_zero
    (A : E2 →L[Real] E2) (p v : E2) (hp : inner Real p p = 1)
    (hv : inner Real p v = 0) : inner Real (circleNormal A p) (A v) = 0 := by
  obtain ⟨a, rfl⟩ := eq_smul_circleQuarterTurn_of_inner_eq_zero p v hp hv
  simp only [map_smul, inner_smul_right, circleNormal,
    inner_circleQuarterTurn_self, mul_zero]

theorem circleNormal_ne_zero
    (A : E2 →L[Real] E2) (p : E2) (hp : inner Real p p = 1)
    (hA : InjOn A {v | inner Real p v = 0}) : circleNormal A p ≠ 0 := by
  have hp0 : p ≠ 0 := by
    intro h
    simp [h] at hp
  have ht : circleQuarterTurn p ≠ 0 := by
    intro h
    apply hp0
    apply circleQuarterTurn.injective
    simpa using h
  have hAt : A (circleQuarterTurn p) ≠ 0 := by
    intro h
    apply ht
    apply hA (inner_self_circleQuarterTurn p) (by simp)
    simpa using h
  intro h
  apply hAt
  apply circleQuarterTurn.injective
  simpa only [circleNormal, map_zero] using h

theorem injective_tangent_add_circleNormal
    (A : E2 →L[Real] E2) (p : E2) (hp : inner Real p p = 1)
    (hA : InjOn A {v | inner Real p v = 0}) :
    Function.Injective fun v =>
      A (v - inner Real p v • p) + inner Real p v • circleNormal A p := by
  have hproj (v : E2) : inner Real p (v - inner Real p v • p) = 0 := by
    simp only [inner_sub_right, inner_smul_right, hp, mul_one, sub_self]
  have hnormal (v : E2) :
      inner Real (circleNormal A p) (A (v - inner Real p v • p)) = 0 :=
    inner_circleNormal_apply_eq_zero A p _ hp (hproj v)
  have hnn : inner Real (circleNormal A p) (circleNormal A p) ≠ 0 := by
    simpa only [ne_eq, inner_self_eq_zero] using circleNormal_ne_zero A p hp hA
  intro u v huv
  dsimp only at huv
  have hdot := congrArg (inner Real (circleNormal A p)) huv
  simp only [inner_add_right, inner_smul_right, hnormal, zero_add] at hdot
  have huv' : inner Real p u = inner Real p v := mul_right_cancel₀ hnn hdot
  have hproj_eq : u - inner Real p u • p = v - inner Real p v • p := by
    apply hA (hproj u) (hproj v)
    exact add_right_cancel (huv.trans (by rw [huv']))
  rwa [huv', sub_left_inj] at hproj_eq

theorem injOn_fderiv_extension_tangent_circle {f : S1 → E2}
    (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ f)
    {G : E2 → E2} (hG : ContDiff Real ∞ G)
    (hrestrict : ∀ p : S1, G p = f p) (p : S1) :
    InjOn (fderiv Real G p) {v : E2 | inner Real (p : E2) v = 0} := by
  let L : TangentSpace (𝓡 1) p →L[Real] E2 :=
    mfderiv (𝓡 1) (𝓡 2) (Subtype.val : S1 → E2) p
  have hrange : L.range = (Real ∙ (p : E2))ᗮ := by
    convert! range_mvfderiv_subtypeVal p
  have hchain : mfderiv (𝓡 1) (𝓡 2) f p = (fderiv Real G p).comp L := by
    have heq : f = G ∘ (Subtype.val : S1 → E2) := funext fun y => (hrestrict y).symm
    rw [heq, mfderiv_comp _ (hG.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
      ((contMDiff_coe_sphere (n := 1) p).mdifferentiableAt
        (show (∞ : ℕ∞ω) ≠ 0 by simp)), mfderiv_eq_fderiv]
  intro u hu v hv huv
  have hu' : u ∈ L.range := by
    rw [hrange, Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact hu
  have hv' : v ∈ L.range := by
    rw [hrange, Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact hv
  obtain ⟨u', rfl⟩ := hu'
  obtain ⟨v', rfl⟩ := hv'
  apply congrArg L
  apply (hf.isImmersion.isImmersionAt p).injective_mfderiv_modelWithCornersSelf (by simp)
  rw [hchain]
  exact huv

end Poincare.Manifold.Schoenflies
