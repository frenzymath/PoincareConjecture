import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.CylinderJetTranslation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)

theorem roundCylinderIteratedDerivative_congr_germ (u : ℝ)
    (c : OpenPartialHomeomorph UnitTwoSphere E₂)
    {B B' : RoundCylinderTwoTensor} {p : RoundCylinderCoordinates}
    (h : ∀ a b : Fin 3,
      (fun y => roundCylinderTensorCoefficient B c y a b) =ᶠ[𝓝 p]
        (fun y => roundCylinderTensorCoefficient B' c y a b))
    (k : ℕ) (a : Fin (2 + k) → Fin 3) :
    (fun y => roundCylinderIteratedDerivative u c B k y a) =ᶠ[𝓝 p]
      (fun y => roundCylinderIteratedDerivative u c B' k y a) := by
  classical
  induction k with
  | zero => exact (h (a 0) (a 1)).sub (Filter.EventuallyEq.refl _ _)
  | succ k ih =>
    have hd := (ih (fun i => a i.succ)).fderiv (𝕜 := ℝ)
    have hv : ∀ᶠ y in 𝓝 p, ∀ i : Fin (2 + k), ∀ d : Fin 3,
        roundCylinderIteratedDerivative u c B k y
          (Function.update (fun l => a l.succ) i d) =
        roundCylinderIteratedDerivative u c B' k y
          (Function.update (fun l => a l.succ) i d) :=
      Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun d =>
        ih (Function.update (fun l => a l.succ) i d)
    filter_upwards [hd, hv] with y hy hvy
    simp only [roundCylinderIteratedDerivative, roundCylinderTensorDerivative]
    congr 1
    · convert! congrArg (fun L => L (roundCylinderCoordinateBasis (a 0))) hy
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro d _
      congr 1
      convert! hvy i d

theorem roundCylinderJetErrorSquared_congr_germ (u : ℝ)
    {B B' : RoundCylinderTwoTensor} (m : ℕ) (z : RoundCylinderSpace)
    (h : ∀ a b : Fin 3,
      (fun y => roundCylinderTensorCoefficient B (chartAt E₂ z.1) y a b) =ᶠ[
        𝓝 ((chartAt E₂ z.1) z.1, z.2)]
      (fun y => roundCylinderTensorCoefficient B' (chartAt E₂ z.1) y a b)) :
    roundCylinderJetErrorSquared u B m z = roundCylinderJetErrorSquared u B' m z := by
  unfold roundCylinderJetErrorSquared
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  funext a
  exact (roundCylinderIteratedDerivative_congr_germ u _ h k a).self_of_nhds

theorem roundCylinderPullback_congr_of_eventuallyEq
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) {f f' : RoundCylinderSpace → M}
    {z : RoundCylinderSpace} (h : f =ᶠ[𝓝 z] f') :
    roundCylinderPullback g f z = roundCylinderPullback g f' z := by
  have hd := h.mfderiv_eq (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) (I' := 𝓡 3)
  funext v w
  simp only [roundCylinderPullback, hd]
  exact congrArg (fun p => g.inner p
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f' z v)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f' z w)) h.self_of_nhds

theorem roundCylinderPullback_comp_axialTranslation
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (f : RoundCylinderSpace → M) (s : ℝ)
    (z : RoundCylinderSpace)
    (hf : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f
      (cylinderAxialTranslation s z)) :
    roundCylinderPullback g (f ∘ cylinderAxialTranslation s) z =
      roundCylinderShift s (roundCylinderPullback g f) z := by
  have hd := mfderiv_comp z hf
    ((cylinderAxialTranslation_contMDiff s).mdifferentiableAt (by simp))
  funext v w
  simp only [roundCylinderPullback, roundCylinderShift, hd, ContinuousLinearMap.comp_apply,
    cylinderAxialTranslation_mfderiv, Function.comp_apply]

end PoincareConjecture.M34
