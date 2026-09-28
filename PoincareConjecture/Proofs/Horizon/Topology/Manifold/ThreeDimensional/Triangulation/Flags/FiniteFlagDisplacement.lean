import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Triangulation.Flags.FiniteFlagBounds
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Triangulation.Polyhedral.FiniteSimplexAltitude

set_option autoImplicit false

open Set Metric
open scoped BigOperators

universe u v

namespace Poincare.Topology

open scoped Classical in
theorem norm_coordinates_le_norm_evaluation_div_altitude
    {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
    (s : Finset E) (a : Real) (ha : 0 < a)
    (halt : ∀ v ∈ s,
      a ≤ infDist v (affineSpan Real ((s.erase v : Finset E) : Set E) : Set E))
    (w : s → Real) (hsum : ∑ v, w v = 0) :
    ‖w‖ ≤ ‖∑ v : s, w v • (v : E)‖ / a := by
  classical
  let W (v : E) : Real := if hv : v ∈ s then w ⟨v, hv⟩ else 0
  have hW (v : s) : W v = w v := by simp only [W, dif_pos v.property]
  have hsumW : ∑ v ∈ s, W v = 0 := by
    rw [← Finset.sum_coe_sort]
    simp only [hW]
    exact hsum
  have hevalW : ∑ v ∈ s, W v • v = ∑ v : s, w v • (v : E) := by
    rw [← Finset.sum_coe_sort]
    simp only [hW]
  apply (pi_norm_le_iff_of_nonneg (div_nonneg (norm_nonneg _) ha.le)).mpr
  intro v
  have h := abs_weight_le_norm_sum_div_altitude s v v.property a ha
    (halt v v.property) W hsumW
  simpa only [hW, hevalW, Real.norm_eq_abs] using h

open scoped Classical in
theorem finite_flag_displacement_bound
    {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
    {I : Type v} [PartialOrder I]
    (s : Finset E) (a : Real) (ha : 0 < a)
    (halt : ∀ v ∈ s,
      a ≤ infDist v (affineSpan Real ((s.erase v : Finset E) : Set E) : Set E))
    (c : I → s → Real) (support : I → Finset s)
    (hc : ∀ i v, c i v ≠ 0 ↔ v ∈ support i)
    (hsupport : ∀ i, (support i).Nonempty)
    (hstrict : ∀ {i j : I}, i < j → support i ⊂ support j)
    (eta : Real) (heta : 0 < eta)
    (hgap : ∀ i v, v ∈ support i → eta ≤ |c i v|)
    (hnorm : ∀ i, ‖c i‖ ≤ 1) (hsumc : ∀ i, ∑ v, c i v = 1)
    (d : I → E) (delta : Real) (hdelta : 0 ≤ delta)
    (t : Finset I) (hchain : ∀ i ∈ t, ∀ j ∈ t, i ≤ j ∨ j ≤ i)
    (hd : ∀ i ∈ t, ‖d i‖ ≤ delta)
    (w : I → Real) (hsumw : ∑ i ∈ t, w i = 0) :
    ‖∑ i ∈ t, w i • d i‖ ≤
      (delta / a * ((1 + eta⁻¹) ^ t.card - 1)) *
        ‖∑ i ∈ t, w i • (∑ v : s, c i v • (v : E))‖ := by
  classical
  let b : s → Real := ∑ i ∈ t, w i • c i
  have hbsum : ∑ v : s, b v = 0 := by
    simp only [b, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hsumc, mul_one]
    exact hsumw
  have heval : (∑ v : s, b v • (v : E)) =
      ∑ i ∈ t, w i • (∑ v : s, c i v • (v : E)) := by
    simp only [b, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul]
    rw [Finset.sum_comm]
    simp only [mul_smul, Finset.smul_sum]
  have hb := norm_coordinates_le_norm_evaluation_div_altitude s a ha halt b hbsum
  rw [heval] at hb
  have hweights := sum_abs_le_of_strict_supports c support hc hsupport hstrict
    eta heta hgap hnorm t hchain w
  have hcoef : 0 ≤ (1 + eta⁻¹) ^ t.card - 1 :=
    sub_nonneg.mpr (one_le_pow₀ (le_add_of_nonneg_right (inv_nonneg.mpr heta.le)))
  calc
    ‖∑ i ∈ t, w i • d i‖ ≤ ∑ i ∈ t, ‖w i • d i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ t, |w i| * delta := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hd i hi) (abs_nonneg _)
    _ = delta * ∑ i ∈ t, |w i| := by
      simp only [mul_comm]
      rw [Finset.mul_sum]
    _ ≤ delta * (((1 + eta⁻¹) ^ t.card - 1) * ‖b‖) :=
      mul_le_mul_of_nonneg_left hweights hdelta
    _ ≤ delta * (((1 + eta⁻¹) ^ t.card - 1) *
        (‖∑ i ∈ t, w i • (∑ v : s, c i v • (v : E))‖ / a)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb hcoef) hdelta
    _ = _ := by ring

end Poincare.Topology
