import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.LocalCalculus
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u v

namespace PoincareConjecture.M60

variable {n m : ℕ} {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) Y]
  [IsManifold (𝓡 n) ∞ X] [IsManifold (𝓡 m) ∞ Y]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "F" => EuclideanSpace ℝ (Fin m)
local notation "TX" => TangentSpace (𝓡 n) (M := X)
local notation "TY" => TangentSpace (𝓡 m) (M := Y)

omit [IsManifold (𝓡 n) ∞ X] in



theorem contMDiffAt_tensorEvaluation_along {k : ℕ}
    {T : CovariantTensorEvaluation m Y k} (hT : IsSmoothCovariantTensor T)
    {f : X → Y} {x : X} (hf : ContMDiffAt (𝓡 n) (𝓡 m) ∞ f x)
    (V : Fin k → (y : X) → TY (f y))
    (hV : ∀ i, ContMDiffAt (𝓡 n) ((𝓡 m).prod 𝓘(ℝ, F)) ∞
      (fun y => (⟨f y, V i y⟩ : TangentBundle (𝓡 m) Y)) x) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => T (f y) (fun i => V i y)) x := by
  classical
  let e := trivializationAt F TY (f x)
  let b := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
  let S := e.localFrame b
  let C := fun (i : Fin k) (j : Fin m) (y : X) =>
    b.repr (e (⟨f y, V i y⟩ : TangentBundle (𝓡 m) Y)).2 j
  have hx : f x ∈ e.baseSet := mem_baseSet_trivializationAt F TY (f x)
  have hc (i : Fin k) (j : Fin m) :
      ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (C i j) x := by
    exact (b.coord j).toContinuousLinearMap.contMDiffAt.comp x
      (contMDiffAt_totalSpace.mp (hV i)).2
  have hs (a : Fin k → Fin m) : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => T (f y) (fun i => S (a i) (f y))) x :=
    ((hT.2 e.baseSet e.open_baseSet (fun i => S (a i))
      (fun i => e.contMDiffOn_localFrame_baseSet ∞ b (a i))).contMDiffAt
        (e.open_baseSet.mem_nhds hx)).comp x hf
  have hsum : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => ∑ a : Fin k → Fin m,
        (∏ i, C i (a i) y) * T (f y) (fun i => S (a i) (f y))) x :=
    ContMDiffAt.sum fun a _ => (ContMDiffAt.prod fun i _ => hc i (a i)).mul (hs a)
  apply hsum.congr_of_eventuallyEq
  filter_upwards [hf.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hx)] with y hy
  obtain ⟨A, hA⟩ := hT.1 (f y)
  simp_rw [hA]
  have hdecomp : (fun i => V i y) =
      (fun i => ∑ j : Fin m, C i j y • S j (f y)) := by
    funext i
    let W := FiberBundle.extend F (V i y)
    have h := e.eq_sum_localFrameCoeff_smul (I := 𝓡 m) (b := b) (s := W) hy
    have hcoeff (j : Fin m) :
        e.localFrameCoeff (𝓡 m) b j (f y) (V i y) = C i j y := by
      simpa only [W, FiberBundle.extend_apply_self, C] using
        (e.localFrameCoeff_eq_coeff (b := b) (s := W) (i := j) hy)
    simpa only [W, FiberBundle.extend_apply_self, hcoeff, S] using h
  rw [hdecomp, A.map_sum]
  simp only [A.map_smul_univ, smul_eq_mul]



noncomputable def tensorPullbackEvaluation {k : ℕ} (f : X → Y)
    (T : CovariantTensorEvaluation m Y k) : CovariantTensorEvaluation n X k :=
  fun x v => T (f x) (fun i => mfderiv (𝓡 n) (𝓡 m) f x (v i))




theorem isSmoothCovariantTensor_pullback {k : ℕ}
    {T : CovariantTensorEvaluation m Y k} (hT : IsSmoothCovariantTensor T)
    {f : X → Y} (hf : ContMDiff (𝓡 n) (𝓡 m) ∞ f) :
    IsSmoothCovariantTensor (tensorPullbackEvaluation (n := n) f T) := by
  constructor
  · intro x
    obtain ⟨A, hA⟩ := hT.1 (f x)
    refine ⟨A.compLinearMap (fun _ => (mfderiv (𝓡 n) (𝓡 m) f x).toLinearMap), ?_⟩
    intro v
    exact hA _
  · intro U hU V hV x hx
    apply ContMDiffAt.contMDiffWithinAt
    apply contMDiffAt_tensorEvaluation_along hT (hf x)
    intro i
    exact ((hf.contMDiff_tangentMap (by simp)) _).comp x
      ((hV i).contMDiffAt (hU.mem_nhds hx))

end PoincareConjecture.M60
