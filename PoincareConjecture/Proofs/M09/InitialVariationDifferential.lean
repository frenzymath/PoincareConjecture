import PoincareConjecture.Proofs.M09.InitialVariationFields

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

local notation "Q" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem initialVectorVariation_field_zero (A : LExponentialFamily F T τmax p)
    (Z W : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax) :
    variationField (initialVectorVariation A Z W b hb hmax).toLVariation 0 = 0 := by
  have hcast (x y : M) (h : x = y) (v : TangentSpace (𝓡 n) x) :
      (h ▸ v : TangentSpace (𝓡 n) y) = (show TangentSpace (𝓡 n) y from v) := by
    cases h
    rfl
  unfold variationField
  rw [hcast]
  have heq : (fun u : ℝ ↦ A.gamma (Z + u • W) 0) = fun _ : ℝ ↦ p :=
    funext fun u ↦ A.gamma_at_zero (Z + u • W)
  have hvelocity := congrArg (fun α : ℝ → M ↦ (curveVelocity (n := n) α 0 : Q)) heq
  exact hvelocity.trans (by simp [curveVelocity])

set_option backward.isDefEq.respectTransparency false in
theorem initialVectorVariation_field_eq_sliceDifferential (A : LExponentialFamily F T τmax p)
    (Z W : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (τ : ℝ) (hτ : 0 < τ) (hτmax : τ < τmax) :
    (variationField (initialVectorVariation A Z W b hb hmax).toLVariation τ : Q) =
      A.sliceDifferential Z τ W := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  have hcast (x y : M) (h : x = y) (v : TangentSpace (𝓡 n) x) :
      (h ▸ v : TangentSpace (𝓡 n) y) = (show TangentSpace (𝓡 n) y from v) := by
    cases h
    rfl
  unfold variationField
  rw [hcast]
  have hdiff := (lExponentialFamily_initialSlice_contMDiffAt A Z τ hτ hτmax).mdifferentiableAt
    (by simp)
  exact curveVelocity_comp_initial_line (fun Y ↦ A.gamma Y τ) Z W hdiff

set_option backward.isDefEq.respectTransparency false in
theorem initialVectorVariation_differential_on_interval (A : LExponentialFamily F T τmax p)
    (Z W : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax) :
    ∀ τ ∈ Set.Icc 0 b,
      ((congrFun (A.path_eq Z b hb hmax) τ) ▸
          variationField (initialVectorVariation A Z W b hb hmax).toLVariation τ :
        TangentSpace (𝓡 n) (A.gamma Z τ)) = A.sliceDifferential Z τ W := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  intro τ hτ
  have hcast (x y : M) (h : x = y) (v : TangentSpace (𝓡 n) x) :
      (h ▸ v : TangentSpace (𝓡 n) y) = (show TangentSpace (𝓡 n) y from v) := by
    cases h
    rfl
  rw [hcast]
  rcases eq_or_lt_of_le hτ.1 with hzero | hpos
  · subst τ
    rw [initialVectorVariation_field_zero]
    have heq : (fun Y : TangentSpace (𝓡 n) p ↦ A.gamma Y 0) = fun _ ↦ p :=
      funext fun Y ↦ A.gamma_at_zero Y
    unfold LExponentialFamily.sliceDifferential
    rw [heq]
    simp
  · exact initialVectorVariation_field_eq_sliceDifferential A Z W b hb hmax τ hpos
      (hτ.2.trans_lt hmax)

end PoincareConjecture.Proofs.M09
