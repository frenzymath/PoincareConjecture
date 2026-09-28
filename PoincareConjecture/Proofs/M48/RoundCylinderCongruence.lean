import PoincareConjecture.Definitions.Ch09.RoundCylinderGeometry










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

section Tensor

variable {epsilon : ℝ} {B B' : RoundCylinderTwoTensor}
  (hB : ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
    ∀ v w, B z v w = B' z v w)

include hB

theorem roundCylinderTensorCoefficient_congr
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    (p : RoundCylinderCoordinates) (hp : p.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (a b : Fin 3) :
    roundCylinderTensorCoefficient B c p a b =
      roundCylinderTensorCoefficient B' c p a b :=
  hB (c.symm p.1, p.2) hp _ _

theorem roundCylinderIteratedDerivative_congr (u : ℝ)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    (k : ℕ) (p : RoundCylinderCoordinates) (hp : p.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (a : Fin (2 + k) → Fin 3) :
    roundCylinderIteratedDerivative u c B k p a =
      roundCylinderIteratedDerivative u c B' k p a := by
  induction k generalizing p with
  | zero =>
      dsimp only [roundCylinderIteratedDerivative]
      rw [roundCylinderTensorCoefficient_congr hB c p hp]
  | succ k ih =>
      dsimp only [roundCylinderIteratedDerivative, roundCylinderTensorDerivative]
      have heq : (fun q => roundCylinderIteratedDerivative u c B k q (fun i => a i.succ))
          =ᶠ[𝓝 p] (fun q => roundCylinderIteratedDerivative u c B' k q (fun i => a i.succ)) :=
        mem_of_superset ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hp⟩)
          (fun q hq => ih q hq.2 _)
      erw [heq.fderiv_eq (𝕜 := ℝ)]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [ih p hp]

theorem roundCylinderJetErrorSquared_congr (u : ℝ) (order : ℕ)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) :
    roundCylinderJetErrorSquared u B order z = roundCylinderJetErrorSquared u B' order z := by
  dsimp only [roundCylinderJetErrorSquared]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  funext a
  exact roundCylinderIteratedDerivative_congr hB u _ k _ hz a

theorem RoundCylinderTensorSmoothOn.congr
    (h : RoundCylinderTensorSmoothOn epsilon B') : RoundCylinderTensorSmoothOn epsilon B := by
  intro q a b
  apply (h q a b).congr
  intro p hp
  exact roundCylinderTensorCoefficient_congr hB _ p hp.2 a b

theorem RoundCylinderClose.congr {u : ℝ} (h : RoundCylinderClose epsilon u B') :
    RoundCylinderClose epsilon u B := by
  rcases h with ⟨hsmooth, bound, hbound, hjet⟩
  refine ⟨hsmooth.congr hB, bound, hbound, ?_⟩
  intro z hz
  rw [roundCylinderJetErrorSquared_congr hB u _ z hz]
  exact hjet z hz

end Tensor

theorem RoundCylinderFamilyClose.congr {epsilon : ℝ} {J : Set ℝ}
    {B B' : ℝ → RoundCylinderTwoTensor}
    (hB : ∀ s ∈ J, ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
      ∀ v w, B s z v w = B' s z v w)
    (h : RoundCylinderFamilyClose epsilon J B') : RoundCylinderFamilyClose epsilon J B := by
  rcases h with ⟨hsmooth, bound, hbound, hjet⟩
  refine ⟨fun s hs => (hsmooth s hs).congr (hB s hs), bound, hbound, ?_⟩
  intro s hs z hz
  rw [roundCylinderJetErrorSquared_congr (hB s hs) s _ z hz]
  exact hjet s hs z hz

end PoincareConjecture
