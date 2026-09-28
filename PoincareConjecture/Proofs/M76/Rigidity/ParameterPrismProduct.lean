import PoincareConjecture.Proofs.M76.Rigidity.ParameterPrismDomain
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonUnmarkedDiskProduct








set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1


def originalParameterPrismBase : D ≃ₜ (D ×ˢ ({0} : Set ℝ)) where
  toFun z := ⟨((z : V2), 0), z.property, rfl⟩
  invFun z := ⟨(z : E).1, z.property.1⟩
  left_inv _ := rfl
  right_inv z := by
    apply Subtype.ext
    have ht : (z : E).2 = 0 := z.property.2
    exact Prod.ext rfl ht.symm
  continuous_toFun := (continuous_subtype_val.prodMk continuous_const).subtype_mk _
  continuous_invFun := (continuous_fst.comp continuous_subtype_val).subtype_mk _



theorem originalParameterPrismBase_finitePL : originalParameterPrismBase.IsFinitePL := by
  let a : V2 →ᴬ[ℝ] E :=
    (ContinuousAffineMap.id ℝ V2).prod (ContinuousAffineMap.const ℝ V2 (0 : ℝ))
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKD, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_unit_cube (ι := Fin 2)
  exact ⟨a, ⟨K, hK, hKD, K.affineOnFaces_affine a⟩, fun _ => rfl⟩




noncomputable def originalParameterPrismProduct :
    HamiltonIndexOne.HamiltonUnmarkedDiskProduct (D ×ˢ I) originalParameterPrismBase := by
  classical
  let f : E →ᴬ[ℝ] E :=
    (ContinuousLinearMap.fst ℝ V2 ℝ).toContinuousAffineMap.prod
      ((1 / 2 : ℝ) • (ContinuousLinearMap.snd ℝ V2 ℝ).toContinuousAffineMap)
  let K := Classical.choose exists_finite_originalParameterPrism
  have hK := (Classical.choose_spec exists_finite_originalParameterPrism).1
  have hKS := (Classical.choose_spec exists_finite_originalParameterPrism).2
  refine {
    map := f
    piecewiseAffine := ⟨K, hK, hKS, K.affineOnFaces_affine f⟩
    injective := ?_
    inside := ?_
    proper := ?_
    central := ?_ }
  · intro x _ y _ hxy
    have hfirst := congrArg (fun z : E => z.1) hxy
    change x.1 = y.1 at hfirst
    have hsecond : (1 / 2 : ℝ) * x.2 = (1 / 2 : ℝ) * y.2 :=
      congrArg (fun z : E => z.2) hxy
    exact Prod.ext hfirst (by linarith)
  · intro x hx
    refine ⟨hx.1, ?_⟩
    change -1 ≤ (1 / 2 : ℝ) * x.2 ∧ (1 / 2 : ℝ) * x.2 ≤ 1
    constructor <;> linarith [hx.2.1, hx.2.2]
  · intro x hx
    rw [originalParameterPrism_frontier]
    change ((x.1 ∈ Q ∧ -1 ≤ (1 / 2 : ℝ) * x.2 ∧ (1 / 2 : ℝ) * x.2 ≤ 1) ∨
      (x.1 ∈ D ∧ ((1 / 2 : ℝ) * x.2 = -1 ∨ (1 / 2 : ℝ) * x.2 = 1))) ↔ x.1 ∈ Q
    constructor
    · rintro (h | h)
      · exact h.1
      · rcases h.2 with h | h <;> linarith [hx.2.1, hx.2.2]
    · intro h
      exact Or.inl ⟨h, by linarith [hx.2.1], by linarith [hx.2.2]⟩
  · intro x
    change ((x : V2), (1 / 2 : ℝ) * 0) = ((x : V2), 0)
    rw [mul_zero]


theorem originalParameterPrismProduct_map (z : E) :
    originalParameterPrismProduct.map z = (z.1, (1 / 2 : ℝ) * z.2) := rfl

end PoincareConjecture.M76
