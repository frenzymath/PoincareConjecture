import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.GradientFrame
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Linearity
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.PartitionOfUnity.Derivative

noncomputable section
set_option autoImplicit false

open scoped InnerProductSpace BigOperators

namespace Poincare.CurvatureIntegral

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

theorem strainer_tilt_norm_bounds
    (u : E) (w : ι → E) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hu : ‖u‖ ≤ 1) (hw : ∀ i, ‖w i‖ ≤ 1) :
    let β := a / ((Fintype.card ι : ℝ) + 1)
    ‖(1 - a) • u + β • ∑ i, w i‖ ≤ 1 ∧
      ‖(1 - a) • u + β • ∑ i, w i - u‖ ≤ 2 * a := by
  classical
  let N := (Fintype.card ι : ℝ)
  let β := a / (N + 1)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hβ : 0 ≤ β := by dsimp only [β]; positivity
  have hβeq : β * (N + 1) = a := by dsimp only [β]; field_simp
  have hβN : β * N ≤ a := by nlinarith only [hβeq, hβ]
  have hsum : ‖∑ i, w i‖ ≤ N := by
    calc
      _ ≤ ∑ i, ‖w i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum fun i _ => hw i
      _ = N := by simp [N]
  have hfirst : 0 ≤ 1 - a := sub_nonneg.mpr ha1
  have hU := norm_add_le ((1 - a) • u) (β • ∑ i, w i)
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hfirst, abs_of_nonneg hβ] at hU
  have hfirstbound := mul_le_mul_of_nonneg_left hu hfirst
  have hsecondbound := mul_le_mul_of_nonneg_left hsum hβ
  refine ⟨by change ‖(1 - a) • u + β • ∑ i, w i‖ ≤ 1; linarith, ?_⟩
  change ‖(1 - a) • u + β • ∑ i, w i - u‖ ≤ 2 * a
  have heq : (1 - a) • u + β • ∑ i, w i - u =
      -(a • u) + β • ∑ i, w i := by module
  rw [heq]
  have hdiff := norm_add_le (-(a • u)) (β • ∑ i, w i)
  rw [norm_neg, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg ha, abs_of_nonneg hβ] at hdiff
  have hmainbound := mul_le_mul_of_nonneg_left hu ha
  linarith

theorem inner_strainer_tilt_le
    (u : E) (v w : ι → E) {ε a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hopposite : ∀ i, ⟪v i, w i⟫_ℝ ≤ -1 + 2 * ε)
    (hcross : ∀ i j, i ≠ j → ⟪w i, v j⟫_ℝ ≤ ε)
    (hu : ∀ i, ⟪u, v i⟫_ℝ ≤ ε) (i : ι) :
    ⟪(1 - a) • u + (a / ((Fintype.card ι : ℝ) + 1)) • ∑ j, w j,
      v i⟫_ℝ ≤ ε - a / ((Fintype.card ι : ℝ) + 1) := by
  classical
  let N := (Fintype.card ι : ℝ)
  let β := a / (N + 1)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hβ : 0 ≤ β := by dsimp only [β]; positivity
  have hβeq : β * (N + 1) = a := by dsimp only [β]; field_simp
  have hsum : (∑ j, ⟪w j, v i⟫_ℝ) ≤ -1 + (N + 1) * ε := by
    have hpoint (j : ι) :
        ⟪w j, v i⟫_ℝ ≤ ε + if j = i then -1 + ε else 0 := by
      by_cases hji : j = i
      · subst j
        rw [if_pos rfl, real_inner_comm]
        linarith [hopposite i]
      · rw [if_neg hji, add_zero]
        exact hcross j i hji
    have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hpoint j)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    dsimp only [N]
    linarith
  change ⟪(1 - a) • u + β • ∑ j, w j, v i⟫_ℝ ≤ ε - β
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, sum_inner]
  calc
    _ ≤ (1 - a) * ε + β * (-1 + (N + 1) * ε) :=
      add_le_add (mul_le_mul_of_nonneg_left (hu i) (sub_nonneg.mpr ha1))
        (mul_le_mul_of_nonneg_left hsum hβ)
    _ = ε - β := by nlinarith only [congrArg (fun a : ℝ => a * ε) hβeq]

theorem abs_inner_le_of_strainer_perturbation
    (u U v : E) {ε η : ℝ} (hv : ‖v‖ ≤ 1)
    (hmove : ‖U - u‖ ≤ η) (hinner : |⟪u, v⟫_ℝ| ≤ ε) :
    |⟪U, v⟫_ℝ| ≤ ε + η := by
  have heq : ⟪U, v⟫_ℝ = ⟪u, v⟫_ℝ + ⟪U - u, v⟫_ℝ := by
    rw [inner_sub_left]
    ring
  have hCS := (abs_real_inner_le_norm (U - u) v).trans
    (mul_le_mul_of_nonneg_left hv (norm_nonneg (U - u)))
  rw [mul_one] at hCS
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add hinner (hCS.trans hmove))

theorem inner_opposite_le_of_strainer_perturbations
    (u z U Z : E) {ε η : ℝ} (hu : ‖u‖ ≤ 1) (hZ : ‖Z‖ ≤ 1)
    (hmoveU : ‖U - u‖ ≤ η) (hmoveZ : ‖Z - z‖ ≤ η)
    (hopposite : ⟪u, z⟫_ℝ ≤ -1 + 2 * ε) :
    ⟪U, Z⟫_ℝ ≤ -1 + 2 * ε + 2 * η := by
  have heq : ⟪U, Z⟫_ℝ =
      ⟪u, z⟫_ℝ + ⟪U - u, Z⟫_ℝ + ⟪u, Z - z⟫_ℝ := by
    rw [inner_sub_left, inner_sub_right]
    ring
  have hU := (le_abs_self ⟪U - u, Z⟫_ℝ).trans
    ((abs_real_inner_le_norm (U - u) Z).trans
      (mul_le_mul_of_nonneg_left hZ (norm_nonneg (U - u))))
  have hW := (le_abs_self ⟪u, Z - z⟫_ℝ).trans
    ((abs_real_inner_le_norm u (Z - z)).trans
      (mul_le_mul_of_nonneg_right hu (norm_nonneg (Z - z))))
  rw [heq]
  nlinarith only [hopposite, hU, hW, hmoveU, hmoveZ]

end Poincare.CurvatureIntegral

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {ι : Type*} [Fintype ι]

private theorem gradient_const_mul_tightening
    (D : LeviCivitaData g) (c : ℝ) (f : M → ℝ) (x : M) :
    D.gradient (fun y => c * f y) x = c • D.gradient f x := by
  apply (g.inner_isInvertible x).injective
  ext v
  simp only [D.inner_gradient, mvfderiv_const_mul, map_smul, smul_apply, smul_eq_mul]

private theorem gradient_sum_tightening
    (D : LeviCivitaData g) (f : ι → M → ℝ)
    (hf : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i)) (x : M) :
    D.gradient (fun y => ∑ i, f i y) x = ∑ i, D.gradient (f i) x := by
  apply (g.inner_isInvertible x).injective
  ext v
  simp only [D.inner_gradient, map_sum, sum_apply]
  exact Poincare.mvfderiv_finset_sum _ f x v
    (fun i _ => (hf i x).mdifferentiableAt (by simp))

omit [Fintype ι] in
private theorem hessian_finset_sum_tightening
    (D : LeviCivitaData g) (f : ι → M → ℝ)
    (hf : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i))
    (s : Finset ι) (x : M) (v w : TangentSpace (𝓡 n) x) :
    D.hessian (fun y => ∑ i ∈ s, f i y) x v w =
      ∑ i ∈ s, D.hessian (f i) x v w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hessian, hessianOnFields, mvfderiv_const]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [D.hessian_add (hf i) (ContMDiff.sum fun j _ => hf j), ih]

theorem strainer_tilt_differential_data
    (D : LeviCivitaData g) (u : M → ℝ) (w : ι → M → ℝ)
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (hw : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (w i)) (a : ℝ) :
    let β := a / ((Fintype.card ι : ℝ) + 1)
    let F := fun y => (1 - a) * u y + β * ∑ i, w i y
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ F ∧
      (∀ x, D.gradient F x =
        (1 - a) • D.gradient u x + β • ∑ i, D.gradient (w i) x) ∧
      ∀ x (v z : TangentSpace (𝓡 n) x),
        D.hessian F x v z =
          (1 - a) * D.hessian u x v z + β * ∑ i, D.hessian (w i) x v z := by
  dsimp only
  have hs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => ∑ i, w i y) :=
    ContMDiff.sum fun i _ => hw i
  have hu' : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => (1 - a) * u y) :=
    contMDiff_const.mul hu
  have hs' : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => (a / ((Fintype.card ι : ℝ) + 1)) * ∑ i, w i y) :=
    contMDiff_const.mul hs
  refine ⟨hu'.add hs', ?_, ?_⟩
  · intro x
    rw [D.gradient_add ((hu' x).mdifferentiableAt (by simp))
      ((hs' x).mdifferentiableAt (by simp)), gradient_const_mul_tightening,
      gradient_const_mul_tightening, gradient_sum_tightening D w hw]
  · intro x v z
    rw [D.hessian_add hu' hs', D.hessian_const_mul, D.hessian_const_mul,
      hessian_finset_sum_tightening D w hw]

theorem smooth_strainer_extension_tightening
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {ι : Type*} [Fintype ι]
    {g : PoincareConjecture.RiemannianMetric n M} (D : PoincareConjecture.LeviCivitaData g)
    (f h : ι → M → ℝ) (u v : M → ℝ)
    (hf : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i))
    (hh : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (h i))
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ v)
    {S : Set M} {ε a H : ℝ} (hε : 0 ≤ ε)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hH : 0 ≤ H)
    (hmargin : ((Fintype.card ι : ℝ) + 1) * ε < a)
    (hunit : ∀ x ∈ S,
      g.tangentNorm x (D.gradient u x) ≤ 1 ∧
      g.tangentNorm x (D.gradient v x) ≤ 1 ∧
      ∀ i, g.tangentNorm x (D.gradient (f i) x) ≤ 1 ∧
        g.tangentNorm x (D.gradient (h i) x) ≤ 1)
    (hpair : ∀ x ∈ S,
      g.inner x (D.gradient u x) (D.gradient v x) ≤ -1 + 2 * ε ∧
      ∀ i, g.inner x (D.gradient (f i) x) (D.gradient (h i) x) ≤ -1 + 2 * ε)
    (holdcross : ∀ x ∈ S, ∀ i j, i ≠ j →
      |g.inner x (D.gradient (h i) x) (D.gradient (f j) x)| ≤ ε)
    (hnewcross : ∀ x ∈ S, ∀ i,
      |g.inner x (D.gradient u x) (D.gradient (f i) x)| ≤ ε ∧
      |g.inner x (D.gradient u x) (D.gradient (h i) x)| ≤ ε ∧
      |g.inner x (D.gradient v x) (D.gradient (f i) x)| ≤ ε ∧
      |g.inner x (D.gradient v x) (D.gradient (h i) x)| ≤ ε)
    (hhess : ∀ x ∈ S, ∀ w : TangentSpace (𝓡 n) x,
      D.hessian u x w w ≤ H * g.inner x w w ∧
      D.hessian v x w w ≤ H * g.inner x w w ∧
      ∀ i, D.hessian (f i) x w w ≤ H * g.inner x w w ∧
        D.hessian (h i) x w w ≤ H * g.inner x w w) :
    let β := a / ((Fintype.card ι : ℝ) + 1)
    let F := fun x => (1 - a) * u x + β * ∑ i, h i x
    let G := fun x => (1 - a) * v x + β * ∑ i, f i x
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ F ∧
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ G ∧
      ∀ x ∈ S,
        (1 - 2 * ε - 4 * a ≤ g.tangentNorm x (D.gradient F x) ∧
          g.tangentNorm x (D.gradient F x) ≤ 1) ∧
        (1 - 2 * ε - 4 * a ≤ g.tangentNorm x (D.gradient G x) ∧
          g.tangentNorm x (D.gradient G x) ≤ 1) ∧
        g.inner x (D.gradient F x) (D.gradient G x) ≤ -1 + 2 * ε + 4 * a ∧
        (∀ i,
          |g.inner x (D.gradient F x) (D.gradient (f i) x)| ≤ ε + 2 * a ∧
          |g.inner x (D.gradient F x) (D.gradient (h i) x)| ≤ ε + 2 * a ∧
          |g.inner x (D.gradient G x) (D.gradient (f i) x)| ≤ ε + 2 * a ∧
          |g.inner x (D.gradient G x) (D.gradient (h i) x)| ≤ ε + 2 * a ∧
          g.inner x (D.gradient F x) (D.gradient (f i) x) ≤ ε - β ∧
          g.inner x (D.gradient F x) (D.gradient (f i) x) < 0) ∧
        ∀ w : TangentSpace (𝓡 n) x,
          D.hessian F x w w ≤ H * g.inner x w w ∧
          D.hessian G x w w ≤ H * g.inner x w w := by
  classical
  let β := a / ((Fintype.card ι : ℝ) + 1)
  let F := fun x => (1 - a) * u x + β * ∑ i, h i x
  let G := fun x => (1 - a) * v x + β * ∑ i, f i x
  obtain ⟨hF, hFgrad, hFhess⟩ := strainer_tilt_differential_data D u h hu hh a
  obtain ⟨hG, hGgrad, hGhess⟩ := strainer_tilt_differential_data D v f hv hf a
  have hden : 0 < (Fintype.card ι : ℝ) + 1 := by positivity
  have hapos : 0 < a := (mul_nonneg hden.le hε).trans_lt hmargin
  have hβ : 0 ≤ β := (div_pos hapos hden).le
  have hβeq : β * ((Fintype.card ι : ℝ) + 1) = a := by
    dsimp only [β]
    field_simp
  have hβmass : (1 - a) + β * (Fintype.card ι : ℝ) ≤ 1 := by
    nlinarith only [hβeq, hβ]
  have hneg : ε - β < 0 := by
    apply sub_neg.mpr
    apply (lt_div_iff₀ hden).mpr
    simpa only [mul_comm] using hmargin
  refine ⟨hF, hG, ?_⟩
  intro x hx
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨hux, hvx, hfx⟩ := hunit x hx
  obtain ⟨huv, hfh⟩ := hpair x hx
  have hFnorm : ‖D.gradient F x‖ ≤ 1 ∧
      ‖D.gradient F x - D.gradient u x‖ ≤ 2 * a := by
    rw [hFgrad x]
    exact Poincare.CurvatureIntegral.strainer_tilt_norm_bounds _ _ ha ha1 hux
      (fun i => (hfx i).2)
  have hGnorm : ‖D.gradient G x‖ ≤ 1 ∧
      ‖D.gradient G x - D.gradient v x‖ ≤ 2 * a := by
    rw [hGgrad x]
    exact Poincare.CurvatureIntegral.strainer_tilt_norm_bounds _ _ ha ha1 hvx
      (fun i => (hfx i).1)
  have hFG : ⟪D.gradient F x, D.gradient G x⟫_ℝ ≤ -1 + 2 * ε + 4 * a := by
    have h := Poincare.CurvatureIntegral.inner_opposite_le_of_strainer_perturbations
      (D.gradient u x) (D.gradient v x) (D.gradient F x) (D.gradient G x)
      hux hGnorm.1 hFnorm.2 hGnorm.2 huv
    linarith only [h]
  have hFlo : 1 - 2 * ε - 4 * a ≤ ‖D.gradient F x‖ := by
    have h := Poincare.CurvatureIntegral.norm_lower_bound_of_opposite_pair
      (D.gradient F x) (D.gradient G x) hGnorm.1
      (show ⟪D.gradient F x, D.gradient G x⟫_ℝ ≤ -1 + 2 * (ε + 2 * a) by linarith)
    linarith only [h]
  have hGlo : 1 - 2 * ε - 4 * a ≤ ‖D.gradient G x‖ := by
    have h := Poincare.CurvatureIntegral.norm_lower_bound_of_opposite_pair
      (D.gradient G x) (D.gradient F x) hFnorm.1
      (show ⟪D.gradient G x, D.gradient F x⟫_ℝ ≤ -1 + 2 * (ε + 2 * a) by
        rw [real_inner_comm]; linarith only [hFG])
    linarith only [h]
  refine ⟨⟨hFlo, hFnorm.1⟩, ⟨hGlo, hGnorm.1⟩, hFG, ?_, ?_⟩
  · intro i
    obtain ⟨huf, huh, hvf, hvh⟩ := hnewcross x hx i
    have htight : ⟪D.gradient F x, D.gradient (f i) x⟫_ℝ ≤ ε - β := by
      rw [hFgrad x]
      exact Poincare.CurvatureIntegral.inner_strainer_tilt_le
        (D.gradient u x) (fun j => D.gradient (f j) x) (fun j => D.gradient (h j) x)
        ha ha1 hfh (fun j k hjk => (abs_le.mp (holdcross x hx j k hjk)).2)
        (fun j => (abs_le.mp (hnewcross x hx j).1).2) i
    exact ⟨Poincare.CurvatureIntegral.abs_inner_le_of_strainer_perturbation
        (D.gradient u x) (D.gradient F x) (D.gradient (f i) x) (hfx i).1 hFnorm.2 huf,
      Poincare.CurvatureIntegral.abs_inner_le_of_strainer_perturbation
        (D.gradient u x) (D.gradient F x) (D.gradient (h i) x) (hfx i).2 hFnorm.2 huh,
      Poincare.CurvatureIntegral.abs_inner_le_of_strainer_perturbation
        (D.gradient v x) (D.gradient G x) (D.gradient (f i) x) (hfx i).1 hGnorm.2 hvf,
      Poincare.CurvatureIntegral.abs_inner_le_of_strainer_perturbation
        (D.gradient v x) (D.gradient G x) (D.gradient (h i) x) (hfx i).2 hGnorm.2 hvh,
      htight, htight.trans_lt hneg⟩
  · intro w
    have hnonneg : 0 ≤ H * g.inner x w w :=
      mul_nonneg hH (show 0 ≤ ⟪w, w⟫_ℝ from real_inner_self_nonneg)
    have hcombine (A : ℝ) (B : ι → ℝ)
        (hA : A ≤ H * g.inner x w w) (hB : ∀ i, B i ≤ H * g.inner x w w) :
        (1 - a) * A + β * ∑ i, B i ≤ H * g.inner x w w := by
      have hsum : (∑ i, B i) ≤ (Fintype.card ι : ℝ) * (H * g.inner x w w) := by
        simpa using (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hB i))
      calc
        _ ≤ (1 - a) * (H * g.inner x w w) +
            β * ((Fintype.card ι : ℝ) * (H * g.inner x w w)) :=
          add_le_add (mul_le_mul_of_nonneg_left hA (sub_nonneg.mpr ha1))
            (mul_le_mul_of_nonneg_left hsum hβ)
        _ = ((1 - a) + β * (Fintype.card ι : ℝ)) * (H * g.inner x w w) := by ring
        _ ≤ 1 * (H * g.inner x w w) := mul_le_mul_of_nonneg_right hβmass hnonneg
        _ = _ := one_mul _
    obtain ⟨huH, hvH, hfhH⟩ := hhess x hx w
    constructor
    · rw [hFhess]
      exact hcombine _ _ huH (fun i => (hfhH i).2)
    · rw [hGhess]
      exact hcombine _ _ hvH (fun i => (hfhH i).1)

end PoincareConjecture.LeviCivitaData
