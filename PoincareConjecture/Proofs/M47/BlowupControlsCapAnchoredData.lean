import PoincareConjecture.Proofs.M47.BlowupControlsCapAffineFields
import PoincareConjecture.Proofs.M47.BlowupControlsCapAnchor
import PoincareConjecture.Proofs.M47.BlowupControlsCapAffineComparison











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}



theorem exists_cap_anchored_neck_data (N : EpsilonNeck g)
    (hsmall : N.epsilon ≤ 1 / 1200) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 200)
    (haccuracy : 6 * N.epsilon ≤ epsilon) (q : UnitTwoSphere) :
    ∃ b : ℝ, ∃ E B : EpsilonNeck g,
      -N.epsilon⁻¹ < b ∧ b + 8 < N.epsilon⁻¹ ∧
      E.epsilon = epsilon ∧ B.epsilon = epsilon ∧
      E.connection = N.connection ∧ B.connection = N.connection ∧
      E.carrier = N.region b N.epsilon⁻¹ ∧ B.carrier ⊆ N.carrier ∧
      B.central_sphere = N.coordinate_map '' (univ ×ˢ ({b} : Set ℝ)) ∧
      N.coordinate_map '' (univ ×ˢ ({b} : Set ℝ)) ⊆
        closure (E.region (-epsilon⁻¹) (-epsilon⁻¹ / 2)) := by
  obtain ⟨c, lambda, b, hc, hlam, hlam_eq, hright, hleft, hb, hb'⟩ :=
    exists_cap_right_anchor N hsmall hepsilon haccuracy q
  have hepsilon_lt : epsilon < 1 / 2 := by linarith
  have hepos : 0 < epsilon⁻¹ := inv_pos.mpr hepsilon
  have hL : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have he : epsilon⁻¹ ≤ N.epsilon⁻¹ / 6 := by
    have hge : N.epsilon * 6 ≤ epsilon := by linarith
    calc
      epsilon⁻¹ = 1 / epsilon := by rw [one_div]
      _ ≤ 1 / (N.epsilon * 6) := one_div_le_one_div_of_le
        (mul_pos N.epsilon_pos (by norm_num)) hge
      _ = N.epsilon⁻¹ / 6 := by field_simp
  have hfac_c := cap_affine_factor_bounds hsmall
    (cap_neck_normalized_scalar_difference N hsmall q hc)
  have hscale_c :
      (N.scale ^ 2 * N.connection.scalarCurvature (N.coordinate_map (q, c))) *
        lambda ^ 2 = 1 := by
    rw [hlam_eq]
    exact hfac_c.2.2.2.2
  have hdomainE : ∀ s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹,
      lambda * s + c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    intro s hs
    constructor
    · nlinarith [hs.1]
    · nlinarith [hs.2]
  have hcloseE := cap_neck_affine_normalized_comparison N hsmall hepsilon
    haccuracy q hc hlam.le hscale_c hdomainE
  have hscalar_c : 0 < N.connection.scalarCurvature (N.coordinate_map (q, c)) := by
    have hsquare : 0 < N.scale ^ 2 := sq_pos_of_pos N.scale_pos
    nlinarith [hfac_c.1]
  let E := capAffineNeck N hepsilon hepsilon_lt hlam hdomainE q hscalar_c hcloseE
  have hE := capAffineNeck_full_fields N hepsilon hepsilon_lt hlam hdomainE q
    hscalar_c hcloseE
  have hEcarrier : E.carrier = N.region b N.epsilon⁻¹ := by
    rw [hE.2.2.1, ← hleft, hright]
  have hbformula : b = N.epsilon⁻¹ - 2 * lambda * epsilon⁻¹ := by
    nlinarith [hright, hleft]
  have hfac_b := cap_affine_factor_bounds hsmall
    (cap_neck_normalized_scalar_difference N hsmall q ⟨hb, hb'⟩)
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
  have hupper_b : lambdab ≤ (101 / 100 : ℝ) := hfac_b.2.2.2.1
  have hdomainB : ∀ s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹,
      lambdab * s + b ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    intro s hs
    have hsl : -lambdab * epsilon⁻¹ < lambdab * s := by
      have h := mul_lt_mul_of_pos_left hs.1 hlambdab
      nlinarith only [h]
    have hsu : lambdab * s < lambdab * epsilon⁻¹ :=
      mul_lt_mul_of_pos_left hs.2 hlambdab
    have hsum : lambdab + 2 * lambda ≤ (303 / 100 : ℝ) := by
      linarith
    have hprod : (lambdab + 2 * lambda) * epsilon⁻¹ ≤ N.epsilon⁻¹ := by
      calc
        (lambdab + 2 * lambda) * epsilon⁻¹ ≤ (303 / 100 : ℝ) * epsilon⁻¹ :=
          mul_le_mul_of_nonneg_right hsum hepos.le
        _ ≤ (303 / 100 : ℝ) * (N.epsilon⁻¹ / 6) :=
          mul_le_mul_of_nonneg_left he (by norm_num)
        _ ≤ N.epsilon⁻¹ := by linarith only [hL]
    have hdiff : (97 / 100 : ℝ) ≤ 2 * lambda - lambdab := by linarith
    have hdiffpos : 0 < (2 * lambda - lambdab) * epsilon⁻¹ :=
      mul_pos (by linarith only [hdiff]) hepos
    constructor
    · calc
        -N.epsilon⁻¹ < N.epsilon⁻¹ - (lambdab + 2 * lambda) * epsilon⁻¹ := by
          linarith only [hprod, hL]
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
    haccuracy q ⟨hb, hb'⟩ hlambdab.le hscale_b hdomainB
  have hscalar_b : 0 < N.connection.scalarCurvature (N.coordinate_map (q, b)) := by
    have hsquare : 0 < N.scale ^ 2 := sq_pos_of_pos N.scale_pos
    nlinarith [hfac_b.1]
  let B := capAffineNeck N hepsilon hepsilon_lt hlambdab hdomainB q hscalar_b hcloseB
  have hB := capAffineNeck_full_fields N hepsilon hepsilon_lt hlambdab hdomainB q
    hscalar_b hcloseB
  have hmargin : b + 8 < N.epsilon⁻¹ := by
    have he200 : (200 : ℝ) ≤ epsilon⁻¹ := by
      have h := inv_anti₀ hepsilon hepsilon_le
      norm_num at h
      exact h
    have hprod1 := mul_le_mul_of_nonneg_right hlower_c hepos.le
    have hprod2 := mul_le_mul_of_nonneg_left he200 (by norm_num : (0 : ℝ) ≤ 99 / 100)
    nlinarith only [hright, hleft, hprod1, hprod2]
  refine ⟨b, E, B, hb, hmargin, hE.1, hB.1, hE.2.1, hB.2.1,
    hEcarrier, ?_, hB.2.2.2.2.2, ?_⟩
  · rw [hB.2.2.1]
    exact fun _ hx => hx.1
  · exact cap_affine_left_sphere_subset_negative_closure N E hepsilon hlam
      ⟨hb, hb'⟩ hright hleft hEcarrier hE.2.2.2.2.1

end PoincareConjecture.M47
