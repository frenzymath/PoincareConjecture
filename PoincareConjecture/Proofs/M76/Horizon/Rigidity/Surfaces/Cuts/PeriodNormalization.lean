import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.OriginalTorusSquareMap
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.PeriodicSquare

variable (p : ℝ) [Fact (0 < p)]

noncomputable def normalizeInterval : Icc (0 : ℝ) p ≃ₜ Icc (0 : ℝ) 1 where
  toFun x := ⟨(x : ℝ) / p, div_nonneg x.property.1 (Fact.out : 0 < p).le,
    (div_le_one (Fact.out : 0 < p)).mpr x.property.2⟩
  invFun x := ⟨p * (x : ℝ), mul_nonneg (Fact.out : 0 < p).le x.property.1,
    by nlinarith [x.property.2, (Fact.out : 0 < p)]⟩
  left_inv x := by
    apply Subtype.ext
    dsimp
    field_simp [ne_of_gt (Fact.out : 0 < p)]
  right_inv x := by
    apply Subtype.ext
    dsimp
    field_simp [ne_of_gt (Fact.out : 0 < p)]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

noncomputable def normalizeSquare : Square p ≃ₜ Square 1 :=
  (normalizeInterval p).prodCongr (normalizeInterval p)

theorem normalizeInterval_projection_eq_iff (x y : Icc (0 : ℝ) p) :
    (((normalizeInterval p x : Icc (0 : ℝ) 1) : ℝ) : AddCircle (1 : ℝ)) =
        (((normalizeInterval p y : Icc (0 : ℝ) 1) : ℝ) : AddCircle (1 : ℝ)) ↔
      ((x : ℝ) : AddCircle p) = ((y : ℝ) : AddCircle p) := by
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  rw [AddCircle.coe_eq_coe_iff_eq_or_endpoints (normalizeInterval p x).property
    (normalizeInterval p y).property,
    AddCircle.coe_eq_coe_iff_eq_or_endpoints x.property y.property]
  have hp : p ≠ 0 := ne_of_gt (Fact.out : 0 < p)
  have hzero (a : ℝ) : a / p = 0 ↔ a = 0 := by simp [hp]
  have hone (a : ℝ) : a / p = 1 ↔ a = p := by rw [div_eq_iff hp, one_mul]
  change (↑x / p = ↑y / p ∨ (↑x / p = 0 ∧ ↑y / p = 1) ∨
    (↑x / p = 1 ∧ ↑y / p = 0)) ↔ _
  simp only [div_left_inj' hp, hzero, hone]

theorem normalizeSquare_projection_eq_iff (z w : Square p) :
    projection 1 (normalizeSquare p z) = projection 1 (normalizeSquare p w) ↔
      projection p z = projection p w := by
  change (_, _) = (_, _) ↔ (_, _) = (_, _)
  rw [Prod.mk.injEq, Prod.mk.injEq]
  exact and_congr (normalizeInterval_projection_eq_iff p z.1 w.1)
    (normalizeInterval_projection_eq_iff p z.2 w.2)

noncomputable def normalizeSquareAffine : (ℝ × ℝ) →ᴬ[ℝ] (ℝ × ℝ) :=
  (p⁻¹) • ContinuousAffineMap.id ℝ (ℝ × ℝ)

theorem normalizeSquareAffine_finitePL :
    FinitePiecewiseAffineOn (normalizeSquareAffine p) (squareCarrier p) := by
  have hball := (isFinitePLBallPair_Icc (Fact.out : 0 < p)).prod
    (isFinitePLBallPair_Icc (Fact.out : 0 < p))
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hball
  exact ⟨K, hK, hKs, K.affineOnFaces_affine (normalizeSquareAffine p)⟩

theorem normalizeSquareAffine_value (z : Square p) :
    normalizeSquareAffine p (z.1, z.2) =
      (((normalizeSquare p z).1 : ℝ), ((normalizeSquare p z).2 : ℝ)) := by
  simp [normalizeSquareAffine, normalizeSquare, normalizeInterval, div_eq_mul_inv, mul_comm]

noncomputable def SourceSquareMap.withPeriod
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : SimplicialComplex ℝ E} (M : SourceSquareMap 1 K) : SourceSquareMap p K := by
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let f : C(Square p, K.space) :=
    M.map.comp ⟨normalizeSquare p, (normalizeSquare p).continuous⟩
  have hsurj : Function.Surjective f := M.surjective.comp (normalizeSquare p).surjective
  have hfib (z w : Square p) : f z = f w ↔ Relation.EqvGen (SidePair p) z w := by
    change M.map (normalizeSquare p z) = M.map (normalizeSquare p w) ↔ _
    rw [M.fibers, ← projection_eq_iff 1, normalizeSquare_projection_eq_iff p,
      projection_eq_iff p]
  refine ⟨f, hsurj, hfib, ?_⟩
  obtain ⟨F, hF, hFv⟩ := M.finite_piecewise_affine
  have hmaps : MapsTo (normalizeSquareAffine p) (squareCarrier p) (squareCarrier 1) := by
    intro z hz
    let t : Square p := (⟨z.1, hz.1⟩, ⟨z.2, hz.2⟩)
    rw [show z = ((t.1 : ℝ), (t.2 : ℝ)) from rfl, normalizeSquareAffine_value]
    exact ⟨(normalizeSquare p t).1.property, (normalizeSquare p t).2.property⟩
  refine ⟨F ∘ normalizeSquareAffine p,
    hF.comp (normalizeSquareAffine_finitePL p) hmaps, ?_⟩
  intro z
  rw [Function.comp_apply, normalizeSquareAffine_value]
  exact hFv (normalizeSquare p z)

end PoincareConjecture.M76.PeriodicSquare
