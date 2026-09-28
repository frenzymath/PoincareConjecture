import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Bounds

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.CapCertificate

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem scalar_le_core_radius_inv_sq (N : CapCertificate g)
    {y : M} (hy : y ∈ N.core) :
    N.connection.scalarCurvature y ≤ (N.core_radius y)⁻¹ ^ 2 := by
  have hball : g.ball y (N.core_radius y) ⊆ N.carrier :=
    fun z hz => N.core_ball_subset y hy (subset_closure hz)
  have hbdd : BddAbove (range (fun z : g.ball y (N.core_radius y) =>
      N.connection.scalarCurvature z.val)) := by
    apply N.scalar_range_bddAbove.mono
    rintro _ ⟨z, rfl⟩
    exact ⟨⟨z, hball z.property⟩, rfl⟩
  have hyball : y ∈ g.ball y (N.core_radius y) := by
    change g.edist y y < ENNReal.ofReal (N.core_radius y)
    simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_self] using
      ENNReal.ofReal_pos.mpr (N.core_radius_pos y hy)
  rw [← N.core_radius_eq y hy]
  exact le_csSup hbdd ⟨⟨y, hyball⟩, rfl⟩

theorem core_radius_lt_of_scalar_lower (N : CapCertificate g)
    {C m L : ℝ} (hC : N.cap_constant ≤ C) (hm : 0 < m) (hL : 0 < L)
    (hscale : C ≤ m * L ^ 2) {p y : M} (hp : p ∈ N.carrier)
    (hscalar : m ≤ N.connection.scalarCurvature p) (hy : y ∈ N.core) :
    N.core_radius y < L := by
  have hr := N.core_radius_pos y hy
  have hCpos := N.cap_constant_pos.trans_le hC
  have hratio := N.scalar_lt_constant_mul (N.core_subset_carrier hy) hp
  have hbound : m < C * (N.core_radius y)⁻¹ ^ 2 :=
    hscalar.trans_lt (hratio.trans_le
      ((mul_le_mul_of_nonneg_right hC
        (N.scalar_pos y (N.core_subset_carrier hy)).le).trans
        (mul_le_mul_of_nonneg_left (N.scalar_le_core_radius_inv_sq hy) hCpos.le)))
  have hsquare : m * (N.core_radius y) ^ 2 < C := by
    have hh := mul_lt_mul_of_pos_right hbound (sq_pos_of_pos hr)
    have heq : C * (N.core_radius y)⁻¹ ^ 2 * (N.core_radius y) ^ 2 = C := by
      field_simp
    rwa [heq] at hh
  have hsq : (N.core_radius y) ^ 2 < L ^ 2 :=
    (mul_lt_mul_iff_right₀ hm).mp (by simpa only [mul_comm m] using hsquare.trans_le hscale)
  nlinarith

end PoincareConjecture.CapCertificate
