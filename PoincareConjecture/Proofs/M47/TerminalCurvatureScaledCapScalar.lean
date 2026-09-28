import PoincareConjecture.Proofs.M47.TerminalCurvatureScaledGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M47

theorem terminalCurvature_scalar_ratio_of_errors {C H r s a b : ℝ}
    (hs : 0 < s) (hcompare : r ≤ C * s) (hfloor : H ≤ r)
    (ha : |a - r| ≤ H / (4 * max 1 C))
    (hb : |b - s| ≤ H / (4 * max 1 C)) :
    0 < b ∧ a ≤ (4 * max 1 C) * b := by
  let A := max 1 C
  have hA1 : (1 : ℝ) ≤ A := le_max_left _ _
  have hA : 0 < A := zero_lt_one.trans_le hA1
  have hcompareA : r ≤ A * s :=
    hcompare.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hs.le)
  have hHA := hfloor.trans hcompareA
  have herror : H / (4 * A) ≤ s / 4 := by
    apply (div_le_div_iff₀ (by positivity : 0 < 4 * A) (by norm_num : (0 : ℝ) < 4)).mpr
    nlinarith only [hHA]
  have htarget : (3 / 4 : ℝ) * s ≤ b := by
    have he := (abs_le.mp (hb.trans herror)).1
    linarith only [he]
  refine ⟨(mul_pos (by norm_num) hs).trans_le htarget, ?_⟩
  have hsource : a ≤ A * s + s / 4 := by
    have he := (abs_le.mp (ha.trans herror)).2
    linarith only [he, hcompareA]
  have hAs : s ≤ A * s := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hA1 hs.le
  have hscaled := mul_le_mul_of_nonneg_left htarget (by positivity : 0 ≤ 4 * A)
  change a ≤ (4 * A) * b
  nlinarith only [hsource, hAs, hscaled, hs.le]

theorem terminalCurvature_scaled_cap_scalar_bounds
    {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (N : CapCertificate g)
    {Q C H J : ℝ} (hQ : 0 < Q) (hC : N.cap_constant ≤ C)
    {x : M} (hx : x ∈ N.core)
    (hlo : H ≤ (rescaledMetric_connection g N.connection Q hQ).scalarCurvature x)
    (hhi : (rescaledMetric_connection g N.connection Q hQ).scalarCurvature x ≤ J) :
    let DQ := rescaledMetric_connection g N.connection Q hQ
    0 < DQ.scalarCurvature N.end_neck.center ∧
      H / C ≤ DQ.scalarCurvature N.end_neck.center ∧
      DQ.scalarCurvature N.end_neck.center ≤ C * J ∧
      DQ.scalarCurvature x ≤ C * DQ.scalarCurvature N.end_neck.center := by
  dsimp only
  simp only [rescaledMetric_scalarCurvature] at hlo hhi ⊢
  have hphysicalLo : Q * H ≤ N.connection.scalarCurvature x := by
    have hh := (le_div_iff₀ hQ).mp (show H ≤ N.connection.scalarCurvature x / Q by
      simpa only [div_eq_mul_inv, mul_comm] using hlo)
    simpa only [mul_comm] using hh
  have hphysicalHi : N.connection.scalarCurvature x ≤ Q * J := by
    have hh := (div_le_iff₀ hQ).mp (show N.connection.scalarCurvature x / Q ≤ J by
      simpa only [div_eq_mul_inv, mul_comm] using hhi)
    simpa only [mul_comm] using hh
  have hbounds := terminalCurvature_cap_end_scalar_bounds N hC hx hphysicalLo hphysicalHi
  have hCpos := N.cap_constant_pos.trans_le hC
  have hend : N.end_neck.center ∈ N.carrier :=
    N.end_neck_subset (N.end_neck.central_sphere_subset N.end_neck.center_on_central_sphere)
  have hRend := N.scalar_pos _ hend
  have hcompare := terminalCurvature_cap_scalar_comparison N hx
  rw [N.end_neck_connection] at hcompare
  refine ⟨mul_pos (inv_pos.mpr hQ) hRend, ?_, ?_, ?_⟩
  · calc
      H / C = Q⁻¹ * ((Q * H) / C) := by field_simp [hQ.ne', hCpos.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left hbounds.1 (inv_nonneg.mpr hQ.le)
  · calc
      _ ≤ Q⁻¹ * (C * (Q * J)) :=
        mul_le_mul_of_nonneg_left hbounds.2 (inv_nonneg.mpr hQ.le)
      _ = C * J := by field_simp [hQ.ne']
  · have hc := hcompare.trans (mul_le_mul_of_nonneg_right hC hRend.le)
    have hh := mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr hQ.le)
    simpa only [mul_left_comm] using hh

end PoincareConjecture.M47
