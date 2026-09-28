import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Basic
import PoincareConjecture.Definitions.Ch09.CanonicalNeighborhoods

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

noncomputable def twoCapDiameterConstant (B : ℝ) : ℝ :=
  2 * B / B ^ (-1 / 2 : ℝ) + 1

theorem twoCapDiameterConstant_pos {B : ℝ} (hB : 0 < B) :
    0 < twoCapDiameterConstant B := by
  unfold twoCapDiameterConstant
  positivity

namespace CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [ConnectedSpace M]
  {g : RiemannianMetric 3 M}

theorem intersection_nonempty_of_cover (A B : CapCertificate g)
    (hcover : A.carrier ∪ B.carrier = univ) :
    (A.carrier ∩ B.carrier).Nonempty := by
  obtain ⟨a, ha⟩ := A.core_nonempty
  obtain ⟨b, hb⟩ := B.core_nonempty
  obtain ⟨z, _, hz⟩ := isPreconnected_univ A.carrier B.carrier
    A.carrier_open B.carrier_open (by rw [hcover])
    ⟨a, mem_univ a, A.core_subset_carrier ha⟩
    ⟨b, mem_univ b, B.core_subset_carrier hb⟩
  exact ⟨z, hz⟩

omit [ConnectedSpace M] in

theorem curvature_scale_le_div (A : CapCertificate g) (D : LeviCivitaData g)
    {B : ℝ} (hB : 0 < B) (hconstant : A.cap_constant ≤ B)
    {x z : M} (hx : x ∈ A.carrier) (hz : z ∈ A.carrier) :
    D.scalarCurvature z ^ (-1 / 2 : ℝ) ≤
      D.scalarCurvature x ^ (-1 / 2 : ℝ) / B ^ (-1 / 2 : ℝ) := by
  have hscalar : D.scalarCurvature x ≤ B * D.scalarCurvature z := by
    rw [← A.connection.scalarCurvature_eq D x,
      ← A.connection.scalarCurvature_eq D z]
    exact (A.scalar_lt_constant_mul hz hx).le.trans
      (mul_le_mul_of_nonneg_right hconstant (A.scalar_pos z hz).le)
  have hxpos : 0 < D.scalarCurvature x := by
    rw [← A.connection.scalarCurvature_eq D x]
    exact A.scalar_pos x hx
  have hzpos : 0 < D.scalarCurvature z := by
    rw [← A.connection.scalarCurvature_eq D z]
    exact A.scalar_pos z hz
  have hpow := Real.rpow_le_rpow_of_nonpos hxpos hscalar
    (by norm_num : (-1 / 2 : ℝ) ≤ 0)
  rw [Real.mul_rpow hB.le hzpos.le] at hpow
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hB _)).mpr
  simpa only [mul_comm] using hpow

theorem metricDiameter_lt_of_two_cap_cover (A B : CapCertificate g)
    (D : LeviCivitaData g) {C : ℝ} (hC : 0 < C)
    (hA : A.cap_constant ≤ C) (hB : B.cap_constant ≤ C)
    (hcover : A.carrier ∪ B.carrier = univ) (x : M) :
    metricDiameter g univ <
      twoCapDiameterConstant C * D.scalarCurvature x ^ (-1 / 2 : ℝ) := by
  obtain ⟨z, hzA, hzB⟩ := A.intersection_nonempty_of_cover B hcover
  have hmem (y : M) : y ∈ A.carrier ∨ y ∈ B.carrier := by
    change y ∈ A.carrier ∪ B.carrier
    rw [hcover]
    exact mem_univ y
  have hdist (y : M) : (g.edist z y).toReal <
      C * D.scalarCurvature z ^ (-1 / 2 : ℝ) := by
    rcases hmem y with hy | hy
    · rw [← A.connection.scalarCurvature_eq D z]
      exact ENNReal.toReal_lt_of_lt_ofReal (A.edist_lt_at_point hA hzA hy)
    · rw [← B.connection.scalarCurvature_eq D z]
      exact ENNReal.toReal_lt_of_lt_ofReal (B.edist_lt_at_point hB hzB hy)
  have hdiam : metricDiameter g univ ≤
      2 * C * D.scalarCurvature z ^ (-1 / 2 : ℝ) := by
    apply csSup_le
    · exact ⟨(g.edist x x).toReal, ⟨(⟨x, mem_univ x⟩, ⟨x, mem_univ x⟩), rfl⟩⟩
    · rintro _ ⟨⟨p, q⟩, rfl⟩
      have htriangle := g.toReal_edist_triangle (p : M) z (q : M)
      have hcomm : g.edist (p : M) z = g.edist z p := by
        let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
          ⟨g.toRiemannianMetric⟩
        exact Manifold.riemannianEDist_comm
      rw [hcomm] at htriangle
      have hp := hdist p
      have hq := hdist q
      dsimp at htriangle hp hq ⊢
      linarith
  have hscale : D.scalarCurvature z ^ (-1 / 2 : ℝ) ≤
      D.scalarCurvature x ^ (-1 / 2 : ℝ) / C ^ (-1 / 2 : ℝ) := by
    rcases hmem x with hx | hx
    · exact A.curvature_scale_le_div D hC hA hx hzA
    · exact B.curvature_scale_le_div D hC hB hx hzB
  have hxpos : 0 < D.scalarCurvature x := by
    rcases hmem x with hx | hx
    · rw [← A.connection.scalarCurvature_eq D x]
      exact A.scalar_pos x hx
    · rw [← B.connection.scalarCurvature_eq D x]
      exact B.scalar_pos x hx
  have hscaled := mul_le_mul_of_nonneg_left hscale (by positivity : 0 ≤ 2 * C)
  apply (hdiam.trans hscaled).trans_lt
  unfold twoCapDiameterConstant
  have hpos := Real.rpow_pos_of_pos hxpos (-1 / 2 : ℝ)
  nlinarith [show 2 * C * (D.scalarCurvature x ^ (-1 / 2 : ℝ) /
      C ^ (-1 / 2 : ℝ)) = (2 * C / C ^ (-1 / 2 : ℝ)) *
      D.scalarCurvature x ^ (-1 / 2 : ℝ) by ring]

end CapCertificate

end PoincareConjecture
