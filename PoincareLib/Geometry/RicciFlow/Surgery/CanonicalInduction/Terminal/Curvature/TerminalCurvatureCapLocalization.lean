import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Terminal.Curvature.TerminalCurvatureStaticGeometry
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Lifetime.CanonicalGeometry.CapPersistenceNormalization

/-!
# Localization of the actual source cap and its end neck

The literal scalar ratio bounds the actual scalar supremum. The frozen
intrinsic diameter then places the complete cap carrier in one ball.
Source: derivations/terminal-curvature-witness-transfer.md, Stage F1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareMT.M47

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

/-- The entire actual cap, including its end neck, lies in one ball
whose radius uses only the fixed cap constant and scalar threshold. -/
theorem terminalCurvature_cap_carrier_subset_ball (N : CapCertificate g)
    {C H : ℝ} (hC : N.cap_constant ≤ C) (hH : 0 < H)
    {x : M} (hx : x ∈ N.core) (hscalar : H ≤ N.connection.scalarCurvature x) :
    N.carrier ⊆ g.ball x (C * H ^ (-1 / 2 : ℝ)) := by
  have hxN := N.core_subset_carrier' hx
  obtain ⟨b, _, hratio⟩ := N.scalar_ratio
  have hbounded : BddAbove (range (fun z : N.carrier => N.connection.scalarCurvature z)) :=
    ⟨b * N.connection.scalarCurvature x, by
      rintro _ ⟨z, rfl⟩
      exact hratio x hxN z z.2⟩
  have hsup : H ≤ scalarCurvatureSupOn g N.connection N.carrier :=
    hscalar.trans (le_csSup hbounded ⟨⟨x, hxN⟩, rfl⟩)
  have hpow := Real.rpow_le_rpow_of_nonpos hH hsup (by norm_num : (-1 / 2 : ℝ) ≤ 0)
  have hradius : N.cap_constant * scalarCurvatureSupOn g N.connection N.carrier ^
      (-1 / 2 : ℝ) ≤ C * H ^ (-1 / 2 : ℝ) :=
    (mul_le_mul_of_nonneg_left hpow N.cap_constant_pos.le).trans
      (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hH.le _))
  intro z hz
  change g.edist x z < ENNReal.ofReal (C * H ^ (-1 / 2 : ℝ))
  exact ((edist_le_intrinsicEDist N.carrier x z).trans
    (intrinsicEDist_le_intrinsicDiameter hxN hz)).trans_lt
      (N.intrinsic_diameter_bound.trans_le (ENNReal.ofReal_le_ofReal hradius))

/-- The same literal end center has uniformly bounded positive scalar
whenever the selected core point has the displayed source scalar bounds. -/
theorem terminalCurvature_cap_end_scalar_bounds (N : CapCertificate g)
    {C H J : ℝ} (hC : N.cap_constant ≤ C) {x : M} (hx : x ∈ N.core)
    (hlo : H ≤ N.connection.scalarCurvature x) (hhi : N.connection.scalarCurvature x ≤ J) :
    H / C ≤ N.connection.scalarCurvature N.end_neck.center ∧
      N.connection.scalarCurvature N.end_neck.center ≤ C * J := by
  have hCpos := N.cap_constant_pos.trans_le hC
  have hxN := N.core_subset_carrier' hx
  have hend : N.end_neck.center ∈ N.carrier :=
    N.end_neck_subset (N.end_neck.central_sphere_subset N.end_neck.center_on_central_sphere)
  have hRc := N.scalar_pos _ hend
  have hRx := N.scalar_pos _ hxN
  have hcompare := terminalCurvature_cap_scalar_comparison N hx
  rw [N.end_neck_connection] at hcompare
  constructor
  · apply (div_le_iff₀ hCpos).mpr
    exact hlo.trans (hcompare.trans (by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hC hRc.le))
  · obtain ⟨b, hb, hratio⟩ := N.scalar_ratio
    calc
      _ ≤ b * N.connection.scalarCurvature x := hratio _ hxN _ hend
      _ ≤ C * N.connection.scalarCurvature x :=
        mul_le_mul_of_nonneg_right (hb.le.trans hC) hRx.le
      _ ≤ C * J := mul_le_mul_of_nonneg_left hhi hCpos.le

end PoincareMT.M47
