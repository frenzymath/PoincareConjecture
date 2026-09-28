import PoincareConjecture.Proofs.Ch01.CurvatureConnection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Metric.UniformScalar
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.LinearScalar
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.ScaleComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem eventually_static_neck_terminal_scalar_ratio
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A)
    {ε l : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 10000000000000) (hl : 0 < l) :
    ∀ᶠ t in 𝓝[<] T,
      ∀ N : EpsilonNeck ((H.terminalFlow P04).metric t),
        N.epsilon = ε → N.carrier ⊆ A →
        l ≤ N.connection.scalarCurvature N.center →
        0 < (H.terminalConnection P04).scalarCurvature N.center ∧
        ∀ x ∈ N.carrier,
          0 < (H.terminalConnection P04).scalarCurvature x ∧
          (H.terminalConnection P04).scalarCurvature x /
            (H.terminalConnection P04).scalarCurvature N.center ≤ 2 ∧
          |(H.terminalConnection P04).scalarCurvature x /
            (H.terminalConnection P04).scalarCurvature N.center - 1| ≤
              2000000000004 * ε := by
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp
    (H.tendstoUniformlyOn_terminal_scalarCurvature P04 hA) (l * ε) (mul_pos hl hε),
    self_mem_nhdsWithin] with t hclose ht
  intro N hNe hNA hlower
  have hs := sq_pos_of_pos N.scale_pos
  have hscale : N.scale ^ 2 * l ≤ 1 :=
    (mul_le_mul_of_nonneg_left hlower hs.le).trans_eq N.scale_sq_mul_scalar_center
  have herror (x : H.regularRegion P04) (hx : x ∈ N.carrier) :
      |N.scale ^ 2 * (H.terminalConnection P04).scalarCurvature x -
        N.scale ^ 2 * N.connection.scalarCurvature x| < ε := by
    have hq : N.connection.scalarCurvature x = H.reference.scalar t x :=
      (N.connection.scalarCurvature_eq ((H.terminalFlow P04).connection t) x).trans
        (H.terminalFlow_scalar_of_ne P04 (ne_of_lt ht) x)
    have hh : |(H.terminalConnection P04).scalarCurvature x -
        N.connection.scalarCurvature x| < l * ε := by
      simpa only [Real.dist_eq, hq] using hclose x (hNA hx)
    rw [← mul_sub, abs_mul, abs_of_pos hs]
    exact (mul_lt_mul_of_pos_left hh hs).trans_le (by nlinarith)
  let d := N.scale ^ 2 * (H.terminalConnection P04).scalarCurvature N.center
  have hd : |d - 1| < ε := by
    simpa only [N.scale_sq_mul_scalar_center] using
      herror N.center (N.central_sphere_subset N.center_on_central_sphere)
  have hdlo : (1 / 2 : ℝ) < d := by linarith [(abs_lt.mp hd).1]
  have hQ : 0 < (H.terminalConnection P04).scalarCurvature N.center := by
    have hp : 0 < d := by linarith
    exact (mul_pos_iff_of_pos_left hs).mp hp
  refine ⟨hQ, ?_⟩
  intro x hx
  let v := N.scale ^ 2 * (H.terminalConnection P04).scalarCurvature x
  have hold := N.scalarCurvature_sub_one_le N.connection
    (show N.epsilon ≤ 1 / 1000000 by rw [hNe]; linarith) x hx
  rw [hNe] at hold
  have hv : |v - 1| ≤ 1000000000001 * ε := by
    have he := herror x hx
    obtain ⟨hel, heu⟩ := abs_lt.mp he
    obtain ⟨hol, hou⟩ := abs_le.mp hold
    exact abs_le.mpr ⟨by dsimp [v]; linarith, by dsimp [v]; linarith⟩
  have hR : 0 < (H.terminalConnection P04).scalarCurvature x := by
    have hvpos : 0 < v := by linarith [(abs_le.mp hv).1]
    exact (mul_pos_iff_of_pos_left hs).mp hvpos
  have hratio : (H.terminalConnection P04).scalarCurvature x /
      (H.terminalConnection P04).scalarCurvature N.center = v / d := by
    dsimp [v, d]
    rw [mul_div_mul_left _ _ hs.ne']
  refine ⟨hR, ?_, ?_⟩
  · rw [hratio, div_le_iff₀ (by linarith : 0 < d)]
    linarith [(abs_le.mp hv).2, (abs_lt.mp hd).1]
  · rw [hratio, div_sub_one (by linarith : d ≠ 0), abs_div,
      abs_of_pos (by linarith : 0 < d), div_le_iff₀ (by linarith : 0 < d)]
    have hdiff : |v - d| ≤ 1000000000002 * ε := by
      obtain ⟨hvl, hvu⟩ := abs_le.mp hv
      obtain ⟨hdl, hdu⟩ := abs_lt.mp hd
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    exact hdiff.trans (by nlinarith)

end PoincareConjecture.SingularTimeAssumptions
