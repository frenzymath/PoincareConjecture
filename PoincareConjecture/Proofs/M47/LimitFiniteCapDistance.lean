import PoincareConjecture.Proofs.M47.TerminalCurvatureScaledGeometry
import PoincareConjecture.Proofs.M34.Standard.CapIntrinsicDiameter
import PoincareConjecture.Proofs.M34.Standard.LocalInverseMetricBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

private theorem cap_intrinsic_diameter_lt
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
    [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (N : CapCertificate g)
    {C H : ℝ} (hC : N.cap_constant ≤ C) (hH : 0 < H)
    {x : M} (hx : x ∈ N.core) (hscalar : H ≤ N.connection.scalarCurvature x) :
    intrinsicDiameter g N.carrier < ENNReal.ofReal (C * H ^ (-1 / 2 : ℝ)) := by
  have hxN := N.core_subset_carrier' hx
  obtain ⟨b, _, hratio⟩ := N.scalar_ratio
  have hbounded : BddAbove (range (fun z : N.carrier => N.connection.scalarCurvature z)) :=
    ⟨b * N.connection.scalarCurvature x, by
      rintro _ ⟨z, rfl⟩
      exact hratio x hxN z z.2⟩
  have hsup : H ≤ scalarCurvatureSupOn g N.connection N.carrier :=
    hscalar.trans (le_csSup hbounded ⟨⟨x, hxN⟩, rfl⟩)
  have hpow := Real.rpow_le_rpow_of_nonpos hH hsup (by norm_num : (-1 / 2 : ℝ) ≤ 0)
  apply N.intrinsic_diameter_bound.trans_le
  apply ENNReal.ofReal_le_ofReal
  exact (mul_le_mul_of_nonneg_left hpow N.cap_constant_pos.le).trans
    (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hH.le _))

theorem limitFinite_cap_end_distance_of_forward_bound
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
    [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    {X : Type v} [TopologicalSpace X] [ChartedSpace E X] [IsManifold (𝓡 3) ∞ X]
    {g : RiemannianMetric 3 M} (h : RiemannianMetric 3 X)
    (N : CapCertificate g) (phi : PartialDiffeomorph (𝓡 3) (𝓡 3) X M ∞)
    {Q C H : ℝ} (hQ : 0 < Q) (hC : N.cap_constant ≤ C) (hH : 0 < H)
    {x : X} (hxsource : x ∈ phi.source) (hx : phi x ∈ N.core)
    (hscalar : Q * H ≤ N.connection.scalarCurvature (phi x))
    (hcapture : N.carrier ⊆ phi.target)
    (hbound : ∀ z ∈ N.carrier, ∀ w : TangentSpace (𝓡 3) (phi.symm z),
      h.tangentNorm (phi.symm z) w ≤
        2 * (rescaledMetric g Q hQ).tangentNorm (phi (phi.symm z))
          (mfderiv (𝓡 3) (𝓡 3) phi (phi.symm z) w)) :
    h.edist x (phi.symm N.end_neck.center) <
      ENNReal.ofReal (2 * C * H ^ (-1 / 2 : ℝ)) := by
  have hfactor : 0 < 2 * Real.sqrt Q := mul_pos two_pos (Real.sqrt_pos.mpr hQ)
  have hinverse (z : M) (hz : z ∈ N.carrier) (w : TangentSpace (𝓡 3) z) :
      h.tangentNorm (phi.symm z) (mfderiv (𝓡 3) (𝓡 3) phi.symm z w) ≤
        (2 * Real.sqrt Q) * g.tangentNorm z w := by
    have hb := h.inverse_tangentNorm_le_of_forward_lower_bound
      (rescaledMetric g Q hQ) phi.toOpenPartialHomeomorph
      (phi.contMDiffOn_toFun.of_le (by simp))
      (phi.contMDiffOn_invFun.of_le (by simp)) (hcapture hz) (hbound z hz) w
    change h.tangentNorm (phi.symm z) (mfderiv (𝓡 3) (𝓡 3) phi.symm z w) ≤
      2 * (rescaledMetric g Q hQ).tangentNorm z w at hb
    simpa only [rescaledMetric_tangentNorm, mul_assoc] using hb
  have hlength := g.intrinsicEDist_image_le_mul h phi.symm N.carrier
    (fun z hz => (phi.contMDiffOn_invFun z (hcapture hz)).contMDiffAt
      (phi.open_target.mem_nhds (hcapture hz)) |>.of_le (by simp))
    hfactor hinverse (phi x) N.end_neck.center
  have hend : N.end_neck.center ∈ N.carrier :=
    N.end_neck_subset (N.end_neck.central_sphere_subset N.end_neck.center_on_central_sphere)
  have hdiam := cap_intrinsic_diameter_lt N hC (mul_pos hQ hH) hx hscalar
  have hpair := intrinsicEDist_le_intrinsicDiameter (g := g) (N.core_subset_carrier' hx) hend
  have hdist := (edist_le_intrinsicEDist (g := h) (phi.symm '' N.carrier)
    (phi.symm (phi x)) (phi.symm N.end_neck.center)).trans hlength
  have hleft : phi.symm (phi x) = x := phi.left_inv hxsource
  rw [hleft] at hdist
  calc
    _ ≤ ENNReal.ofReal (2 * Real.sqrt Q) * intrinsicDiameter g N.carrier :=
      hdist.trans (mul_le_mul_right hpair _)
    _ < ENNReal.ofReal (2 * Real.sqrt Q) *
        ENNReal.ofReal (C * (Q * H) ^ (-1 / 2 : ℝ)) :=
      ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr hfactor).ne'
        ENNReal.ofReal_ne_top hdiam
    _ = _ := by
      rw [← ENNReal.ofReal_mul hfactor.le]
      congr 1
      calc
        (2 * Real.sqrt Q) * (C * (Q * H) ^ (-1 / 2 : ℝ)) =
            (2 * C) * (Real.sqrt Q * (Q * H) ^ (-1 / 2 : ℝ)) := by ring
        _ = _ := by rw [terminalCurvature_scaled_scalar_radius hQ hH]

end PoincareConjecture.M47
