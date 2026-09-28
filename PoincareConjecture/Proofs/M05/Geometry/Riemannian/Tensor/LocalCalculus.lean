
import PoincareConjecture.Definitions.Ch01.TensorRegularity
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.Algebra.Structures








set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle Filter Set

universe u

namespace PoincareConjecture.IsSmoothCovariantTensor

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


lemma contMDiffAt_apply {k : ℕ} {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T)
    {X : Fin k → (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hX : ∀ i, ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (X i)) x) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => T y (fun i => X i y)) x := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let V := TangentSpace (𝓡 n) (M := M)
  let e := trivializationAt E V x
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let S := e.localFrame b
  let C := e.localFrameCoeff (𝓡 n) b
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E V x
  have hc (i : Fin k) (j : Fin n) : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => C j y (X i y)) x := contMDiffAt_localFrameCoeff b hx (hX i) j
  have hs (a : Fin k → Fin n) : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => T y (fun i => S (a i) y)) x :=
    (hT.2 e.baseSet e.open_baseSet (fun i => S (a i))
      (fun i => e.contMDiffOn_localFrame_baseSet ∞ b (a i))).contMDiffAt
        (e.open_baseSet.mem_nhds hx)
  have hsum : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => ∑ a : Fin k → Fin n,
        (∏ i, C (a i) y (X i y)) * T y (fun i => S (a i) y)) x :=
    ContMDiffAt.sum fun a _ => (ContMDiffAt.prod fun i _ => hc i (a i)).mul (hs a)
  apply hsum.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  obtain ⟨A, hA⟩ := hT.1 y
  simp_rw [hA]
  have hdecomp : (fun i => X i y) =
      (fun i => ∑ j : Fin n, C j y (X i y) • S j y) := by
    funext i
    exact e.eq_sum_localFrameCoeff_smul (I := 𝓡 n) (b := b) hy
  rw [hdecomp, A.map_sum]
  simp only [A.map_smul_univ, smul_eq_mul]

set_option backward.isDefEq.respectTransparency false in

lemma mdifferentiableAt_apply {k : ℕ} {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T)
    {X : Fin k → (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hX : ∀ i, MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% (X i)) x) :
    MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (fun y => T y (fun i => X i y)) x := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let V := TangentSpace (𝓡 n) (M := M)
  let e := trivializationAt E V x
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let S := e.localFrame b
  let C := e.localFrameCoeff (𝓡 n) b
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E V x
  have hc (i : Fin k) (j : Fin n) : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y => C j y (X i y)) x := mdifferentiableAt_localFrameCoeff b hx (hX i) j
  have hs (a : Fin k → Fin n) : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y => T y (fun i => S (a i) y)) x :=
    ((hT.2 e.baseSet e.open_baseSet (fun i => S (a i))
      (fun i => e.contMDiffOn_localFrame_baseSet ∞ b (a i))).contMDiffAt
        (e.open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
  have hsum : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y => ∑ a : Fin k → Fin n,
        (∏ i, C (a i) y (X i y)) * T y (fun i => S (a i) y)) x := by
    have hp (a : Fin k → Fin n) : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
        (fun y => ∏ i, C (a i) y (X i y)) x := by
      convert (MDifferentiableAt.prod (t := Finset.univ) fun i _ => hc i (a i)) using 1 <;>
        first | rfl | (ext y; simp only [Finset.prod_apply])
    convert (MDifferentiableAt.sum (t := Finset.univ) fun a _ => (hp a).mul (hs a)) using 1 <;>
      first | rfl | (ext y; simp only [Finset.sum_apply, Pi.mul_apply])
  apply hsum.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  obtain ⟨A, hA⟩ := hT.1 y
  simp_rw [hA]
  have hdecomp : (fun i => X i y) =
      (fun i => ∑ j : Fin n, C j y (X i y) • S j y) := by
    funext i
    exact e.eq_sum_localFrameCoeff_smul (I := 𝓡 n) (b := b) hy
  rw [hdecomp, A.map_sum]
  simp only [A.map_smul_univ, smul_eq_mul]

end PoincareConjecture.IsSmoothCovariantTensor
