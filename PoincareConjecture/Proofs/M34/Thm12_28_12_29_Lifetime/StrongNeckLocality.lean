import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff BigOperators Topology

namespace PoincareConjecture.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)

theorem roundCylinderIteratedDerivative_eq_of_eqOn_cylinder
    {epsilon : ℝ} {B D : RoundCylinderTwoTensor}
    (hBD : ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
      ∀ v w : RoundCylinderTangent z, B z v w = D z v w)
    (u : ℝ) (q : UnitTwoSphere) (k : ℕ)
    {x : RoundCylinderCoordinates} (hx : x.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (a : Fin (2 + k) → Fin 3) :
    roundCylinderIteratedDerivative u (chartAt E₂ q) B k x a =
      roundCylinderIteratedDerivative u (chartAt E₂ q) D k x a := by
  induction k generalizing x with
  | zero =>
    dsimp only [roundCylinderIteratedDerivative, roundCylinderTensorCoefficient]
    rw [hBD ((chartAt E₂ q).symm x.1, x.2) hx]
  | succ k ih =>
    have heq : (fun y => roundCylinderIteratedDerivative u (chartAt E₂ q) B k y
        (fun i => a i.succ)) =ᶠ[𝓝 x]
        (fun y => roundCylinderIteratedDerivative u (chartAt E₂ q) D k y
          (fun i => a i.succ)) := by
      filter_upwards [(isOpen_univ.prod isOpen_Ioo).mem_nhds
        (show x ∈ (univ : Set E₂) ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ from ⟨mem_univ _, hx⟩)]
        with y hy
      exact ih hy.2 _
    dsimp only [roundCylinderIteratedDerivative, roundCylinderTensorDerivative]
    apply congrArg₂ (fun v w : ℝ => v - w)
    · exact congrArg (fun L : RoundCylinderCoordinates →L[ℝ] ℝ =>
        L (roundCylinderCoordinateBasis (a 0))) (heq.fderiv_eq (𝕜 := ℝ))
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro d _
      exact congrArg (fun v : ℝ =>
        roundCylinderChristoffel u (chartAt E₂ q) x d (a 0) (a i.succ) * v)
        (ih hx (Function.update (fun j => a j.succ) i d))

theorem roundCylinderJetErrorSquared_eq_of_eqOn_cylinder
    {epsilon : ℝ} {B D : RoundCylinderTwoTensor}
    (hBD : ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
      ∀ v w : RoundCylinderTangent z, B z v w = D z v w)
    (u : ℝ) (m : ℕ) {z : RoundCylinderSpace}
    (hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) :
    roundCylinderJetErrorSquared u B m z = roundCylinderJetErrorSquared u D m z := by
  unfold roundCylinderJetErrorSquared
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  funext a
  exact roundCylinderIteratedDerivative_eq_of_eqOn_cylinder hBD u z.1 k hz a

end PoincareConjecture.M34

namespace PoincareConjecture.RoundCylinderTensorSmoothOn

theorem congr_cylinder {epsilon : ℝ} {B D : RoundCylinderTwoTensor}
    (hB : RoundCylinderTensorSmoothOn epsilon B)
    (hBD : ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
      ∀ v w : RoundCylinderTangent z, B z v w = D z v w) :
    RoundCylinderTensorSmoothOn epsilon D := by
  intro q a b
  apply (hB q a b).congr
  intro x hx
  exact (hBD _ hx.2 _ _).symm

end PoincareConjecture.RoundCylinderTensorSmoothOn

namespace PoincareConjecture.RoundCylinderFamilyClose

theorem congr_cylinder {epsilon : ℝ} {I : Set ℝ}
    {B D : ℝ → RoundCylinderTwoTensor}
    (hB : RoundCylinderFamilyClose epsilon I B)
    (hBD : ∀ u ∈ I, ∀ z : RoundCylinderSpace,
      z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
      ∀ v w : RoundCylinderTangent z, B u z v w = D u z v w) :
    RoundCylinderFamilyClose epsilon I D := by
  obtain ⟨hs, b, hb, hbound⟩ := hB
  refine ⟨fun u hu => (hs u hu).congr_cylinder (hBD u hu), b, hb, ?_⟩
  intro u hu z hz
  rw [← M34.roundCylinderJetErrorSquared_eq_of_eqOn_cylinder (hBD u hu) u _ hz]
  exact hbound u hu z hz

end PoincareConjecture.RoundCylinderFamilyClose
