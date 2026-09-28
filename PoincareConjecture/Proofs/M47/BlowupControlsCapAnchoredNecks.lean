import PoincareConjecture.Proofs.M47.BlowupControlsCapNeckConstructor
import PoincareConjecture.Proofs.M47.BlowupControlsCapAnchor
import PoincareConjecture.Proofs.M47.BlowupControlsCapAffineComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem exists_cap_anchored_necks (N : EpsilonNeck g)
    (hsmall : N.epsilon ≤ 1 / 1200)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (haccuracy : 6 * N.epsilon ≤ epsilon) (hepsilon_lt : epsilon < 1 / 2)
    (q : UnitTwoSphere) :
    ∃ c lambda b : ℝ,
      c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ ∧ 0 < lambda ∧
      lambda = (N.scale ^ 2 * N.connection.scalarCurvature
        (N.coordinate_map (q, c))) ^ (-1 / 2 : ℝ) ∧
      c + lambda * epsilon⁻¹ = N.epsilon⁻¹ ∧
      b = c - lambda * epsilon⁻¹ ∧
      -N.epsilon⁻¹ < b ∧ b < N.epsilon⁻¹ ∧
      ∃ E B : EpsilonNeck g,
        E.epsilon = epsilon ∧ B.epsilon = epsilon ∧
        E.center = N.coordinate_map (q, c) ∧
        B.center = N.coordinate_map (q, b) ∧
        E.carrier = N.region b N.epsilon⁻¹ := by
  obtain ⟨c, lambda, b, hc, hlam, hlam_eq, hright, hbleft, hbneg, hbpos⟩ :=
    exists_cap_right_anchor N hsmall hepsilon haccuracy q
  have hfac_c := cap_affine_factor_bounds hsmall
    (cap_neck_normalized_scalar_difference N hsmall q hc)
  have hscale_c :
      (N.scale ^ 2 * N.connection.scalarCurvature (N.coordinate_map (q, c))) *
        lambda ^ 2 = 1 := by
    rw [hlam_eq]
    exact hfac_c.2.2.2.2
  have hepos : 0 < epsilon⁻¹ := inv_pos.mpr hepsilon
  have he : epsilon⁻¹ ≤ N.epsilon⁻¹ / 6 := by
    have hge : N.epsilon * 6 ≤ epsilon := by linarith
    calc
      epsilon⁻¹ = 1 / epsilon := by rw [one_div]
      _ ≤ 1 / (N.epsilon * 6) := one_div_le_one_div_of_le
        (mul_pos N.epsilon_pos (by norm_num)) hge
      _ = N.epsilon⁻¹ / 6 := by field_simp
  have hdomainE : ∀ s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹,
      lambda * s + c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    intro s hs
    constructor
    · have h := hbleft
      have h' := hbneg
      nlinarith [hs.1, hlam, hepos]
    · nlinarith [hright, hlam, hs.2, hepos]
  have hcloseE := cap_neck_affine_normalized_comparison N hsmall hepsilon
    haccuracy q hc hlam.le hscale_c hdomainE
  have hscalar_c : 0 < N.connection.scalarCurvature (N.coordinate_map (q, c)) := by
    have hsquare : 0 < N.scale ^ 2 := sq_pos_of_pos N.scale_pos
    nlinarith [hfac_c.1]
  let E := capAffineNeck N hepsilon hepsilon_lt hlam hdomainE q
    hscalar_c hcloseE
  have hbformula : b = N.epsilon⁻¹ - 2 * lambda * epsilon⁻¹ := by
    nlinarith [hright, hbleft]
  have hfac_b := cap_affine_factor_bounds hsmall
    (cap_neck_normalized_scalar_difference N hsmall q ⟨hbneg, hbpos⟩)
  let lambdab :=
    (N.scale ^ 2 * N.connection.scalarCurvature (N.coordinate_map (q, b))) ^
      (-1 / 2 : ℝ)
  have hlambdab : 0 < lambdab := hfac_b.2.1
  have hlower_c : (99 / 100 : ℝ) ≤ lambda := by
    rw [hlam_eq]
    exact hfac_c.2.2.1
  have hupper_c : lambda ≤ (101 / 100 : ℝ) := by
    rw [hlam_eq]
    exact hfac_c.2.2.2.1
  have hlower_b : (99 / 100 : ℝ) ≤ lambdab := by
    dsimp [lambdab]
    exact hfac_b.2.2.1
  have hupper_b : lambdab ≤ (101 / 100 : ℝ) := by
    dsimp [lambdab]
    exact hfac_b.2.2.2.1
  have hdomainB : ∀ s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹,
      lambdab * s + b ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    intro s hs
    have hsl : -lambdab * epsilon⁻¹ < lambdab * s := by
      have h := mul_lt_mul_of_pos_left hs.1 hlambdab
      calc
        -lambdab * epsilon⁻¹ = -(lambdab * epsilon⁻¹) := by ring
        _ = lambdab * (-epsilon⁻¹) := by ring
        _ < lambdab * s := h
    have hsu : lambdab * s < lambdab * epsilon⁻¹ := by
      have h := mul_lt_mul_of_pos_left hs.2 hlambdab
      exact h
    have hL : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
    have hsum : lambdab + 2 * lambda ≤ (303 / 100 : ℝ) := by
      nlinarith [hupper_b, hupper_c]
    have hprod : (lambdab + 2 * lambda) * epsilon⁻¹ ≤ N.epsilon⁻¹ := by
      calc
        (lambdab + 2 * lambda) * epsilon⁻¹ ≤
            (303 / 100 : ℝ) * epsilon⁻¹ :=
          mul_le_mul_of_nonneg_right hsum (le_of_lt hepos)
        _ ≤ (303 / 100 : ℝ) * (N.epsilon⁻¹ / 6) :=
          mul_le_mul_of_nonneg_left he (by norm_num)
        _ ≤ N.epsilon⁻¹ := by linarith only [hL]
    have hdiff : (97 / 100 : ℝ) ≤ 2 * lambda - lambdab := by
      linarith [hlower_c, hupper_b]
    have hdiffpos0 : 0 < 2 * lambda - lambdab := by
      linarith [hdiff]
    have hdiffpos : 0 < (2 * lambda - lambdab) * epsilon⁻¹ :=
      mul_pos hdiffpos0 hepos
    constructor
    · calc
        -N.epsilon⁻¹ < N.epsilon⁻¹ -
            (lambdab + 2 * lambda) * epsilon⁻¹ := by linarith only [hprod, hL]
        _ = -lambdab * epsilon⁻¹ + b := by rw [hbformula]; ring
        _ < lambdab * s + b := by linarith only [hsl]
    · calc
        lambdab * s + b < lambdab * epsilon⁻¹ + b := by linarith only [hsu]
        _ = N.epsilon⁻¹ - (2 * lambda - lambdab) * epsilon⁻¹ := by
          rw [hbformula]
          ring
        _ < N.epsilon⁻¹ := by linarith only [hdiffpos]
  have hscale_b :
      (N.scale ^ 2 * N.connection.scalarCurvature (N.coordinate_map (q, b))) *
        lambdab ^ 2 = 1 := hfac_b.2.2.2.2
  have hcloseB := cap_neck_affine_normalized_comparison N hsmall hepsilon
    haccuracy q ⟨hbneg, hbpos⟩ hlambdab.le hscale_b hdomainB
  have hscalar_b : 0 < N.connection.scalarCurvature (N.coordinate_map (q, b)) := by
    have hsquare : 0 < N.scale ^ 2 := sq_pos_of_pos N.scale_pos
    nlinarith [hfac_b.1]
  let B := capAffineNeck N hepsilon hepsilon_lt hlambdab hdomainB q
    hscalar_b hcloseB
  refine ⟨c, lambda, b, hc, hlam, hlam_eq, hright, hbleft, hbneg, hbpos,
    E, B, rfl, rfl, rfl, rfl, ?_⟩
  change N.region (c - lambda * epsilon⁻¹) (c + lambda * epsilon⁻¹) =
    N.region b N.epsilon⁻¹
  rw [hbleft, hright]

end PoincareConjecture.M47
