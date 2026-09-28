import PoincareConjecture.Proofs.M47.BlowupControlsCapAffineFactor

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

private theorem anchor_interval_bounds {gamma epsilon : ℝ}
    (hgamma : 0 < gamma) (haccuracy : 6 * gamma ≤ epsilon) :
    -gamma⁻¹ < gamma⁻¹ - (101 / 100 : ℝ) * epsilon⁻¹ ∧
    gamma⁻¹ - (101 / 100 : ℝ) * epsilon⁻¹ ≤
      gamma⁻¹ - (99 / 100 : ℝ) * epsilon⁻¹ ∧
    gamma⁻¹ - (99 / 100 : ℝ) * epsilon⁻¹ < gamma⁻¹ := by
  have he : epsilon⁻¹ ≤ gamma⁻¹ / 6 := by
    have hge : gamma * 6 ≤ epsilon := by linarith
    calc
      epsilon⁻¹ = 1 / epsilon := by rw [one_div]
      _ ≤ 1 / (gamma * 6) := one_div_le_one_div_of_le
        (mul_pos hgamma (by norm_num)) hge
      _ = gamma⁻¹ / 6 := by field_simp
  have hL : 0 < gamma⁻¹ := inv_pos.mpr hgamma
  have hepos : 0 < epsilon⁻¹ := by
    have : 0 < epsilon := by linarith
    exact inv_pos.mpr this
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

theorem exists_cap_right_anchor (N : EpsilonNeck g)
    (hsmall : N.epsilon ≤ 1 / 1200)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (haccuracy : 6 * N.epsilon ≤ epsilon) (q : UnitTwoSphere) :
    ∃ c lambda b : ℝ,
      c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ ∧
      0 < lambda ∧
      lambda = (N.scale ^ 2 * N.connection.scalarCurvature
        (N.coordinate_map (q, c))) ^ (-1 / 2 : ℝ) ∧
      c + lambda * epsilon⁻¹ = N.epsilon⁻¹ ∧
      b = c - lambda * epsilon⁻¹ ∧
      -N.epsilon⁻¹ < b ∧ b < N.epsilon⁻¹ := by
  have he : epsilon⁻¹ ≤ N.epsilon⁻¹ / 6 := by
    have hge : N.epsilon * 6 ≤ epsilon := by linarith
    calc
      epsilon⁻¹ = 1 / epsilon := by rw [one_div]
      _ ≤ 1 / (N.epsilon * 6) := one_div_le_one_div_of_le
        (mul_pos N.epsilon_pos (by norm_num)) hge
      _ = N.epsilon⁻¹ / 6 := by field_simp
  let L := N.epsilon⁻¹
  let e := epsilon⁻¹
  let a := L - (101 / 100 : ℝ) * e
  let b0 := L - (99 / 100 : ℝ) * e
  have hepos : 0 < epsilon⁻¹ := inv_pos.mpr hepsilon
  have hJ := anchor_interval_bounds N.epsilon_pos haccuracy
  have hsub (c : ℝ) (hc : c ∈ Icc a b0) :
      c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    dsimp [a, b0, L, e] at hc ⊢
    have hL : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
    rcases hc with ⟨hca, hcb⟩
    have hcpos : 0 < c := by nlinarith [hca, hL, he]
    constructor
    · linarith
    · nlinarith [hcb, hepos]
  let lam : ℝ → ℝ := fun c =>
    (N.scale ^ 2 * N.connection.scalarCurvature (N.coordinate_map (q, c))) ^
      (-1 / 2 : ℝ)
  have hlamcont : ContinuousOn lam (Icc a b0) := by
    apply (cap_neck_affine_factor_continuousOn N hsmall q).mono
    intro c hc
    exact hsub c hc
  let f : ℝ → ℝ := fun c => c + lam c * e
  have hfcont : ContinuousOn f (Icc a b0) :=
    (continuousOn_id.add (hlamcont.mul continuousOn_const)).congr
      (fun _ _ => by rfl)
  have hends := hJ
  have hfa : f a ≤ L := by
    have hla := cap_affine_factor_bounds hsmall
      (cap_neck_normalized_scalar_difference N hsmall q
        (hsub a ⟨le_rfl, hends.2.1⟩))
    change a + lam a * e ≤ L
    dsimp [a, e, L, lam]
    nlinarith [hla.2.2.2, hepos]
  have hfb : L ≤ f b0 := by
    have hlb := cap_affine_factor_bounds hsmall
      (cap_neck_normalized_scalar_difference N hsmall q
        (hsub b0 ⟨hends.2.1, le_rfl⟩))
    change L ≤ b0 + lam b0 * e
    dsimp [b0, e, L, lam]
    nlinarith [hlb.2.2.1, hepos]
  have himg : L ∈ f '' Icc a b0 := by
    apply (intermediate_value_Icc hends.2.1 hfcont)
    exact ⟨hfa, hfb⟩
  obtain ⟨c, hc, hfc⟩ := himg
  let lambda := lam c
  let b := c - lambda * e
  have hcb : b = c - lambda * epsilon⁻¹ := by rfl
  have hcl : c + lambda * epsilon⁻¹ = N.epsilon⁻¹ := by
    exact hfc
  have hbound : b ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    have hl := cap_affine_factor_bounds hsmall
      (cap_neck_normalized_scalar_difference N hsmall q (hsub c hc))
    have hL : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
    have hle : epsilon⁻¹ ≤ N.epsilon⁻¹ / 6 := he
    change -N.epsilon⁻¹ < c - lam c * epsilon⁻¹ ∧
      c - lam c * epsilon⁻¹ < N.epsilon⁻¹
    dsimp [lam]
    rcases hc with ⟨hclower, hcupper⟩
    dsimp [a, b0, L, e] at hclower hcupper
    have hcpos : 0 < c := by nlinarith [hclower, hL, he]
    constructor <;> nlinarith [hl.2.2.1, hl.2.2.2, hclower, hcupper, he, hepos, hcpos]
  refine ⟨c, lambda, b, hsub c hc,
    (cap_affine_factor_bounds hsmall
      (cap_neck_normalized_scalar_difference N hsmall q (hsub c hc))).2.1,
    rfl, hcl, hcb, hbound.1, hbound.2⟩

end PoincareConjecture.M47
