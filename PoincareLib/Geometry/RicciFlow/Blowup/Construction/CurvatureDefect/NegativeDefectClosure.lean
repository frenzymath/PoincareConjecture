import PoincareLib.Geometry.RicciFlow.Blowup.Construction.SourceNames
import PoincareLib.Geometry.Riemannian.Curvature.IntrinsicCalculus
import PoincareLib.Geometry.Riemannian.Curvature.ThreeDimensional
import PoincareLib.Geometry.Riemannian.Connection.ScalarJets
import PoincareLib.Geometry.Riemannian.Curvature.Euclidean
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Curvature.Conformal.ConformalPinching
import PoincareLib.Geometry.Riemannian.Curvature.Bounds.Sectional

/-!
# Curvature-operator nonnegativity from vanishing negative defect

Morgan--Tian Theorem 5.33, pp. 99--100, and Theorem 11.8, p. 272, use the
vanishing negative part to obtain nonnegative curvature in a smooth limit.
Here second scalar metric jets give the actual tensor limits, and the
existing three-dimensional operator representation gives the frozen
curvature-operator quadratic inequality.

See `proof-work/tasks/M30/derivations/vanishing-negative-defect-closure.md`.
-/

set_option autoImplicit false

open Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareMT.M30

-- Preserve the reviewed finite-basis telescope of the scalar metric-jet donor.
set_option linter.unusedFintypeInType false in
/-- Second scalar metric jets and vanishing native negative curvature part
give nonnegative curvature operator for the actual target connection
(Morgan--Tian Theorem 5.33, pp. 99--100; Theorem 11.8, p. 272). -/
theorem nonnegativeCurvatureOperator_of_scalar_metric_jets_of_vanishing_defect
    {alpha : Type*} {l : Filter alpha} [l.NeBot]
    {gseq : alpha → RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))}
    {g : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))}
    (Dseq : ∀ i, LeviCivitaData (gseq i)) (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin 3))
    {iota : Type*} [Fintype iota]
    (b : Module.Basis iota ℝ (EuclideanSpace ℝ (Fin 3)))
    (hjets : ∀ r : ℕ, r ≤ 2 → ∀ a c : iota,
      Tendsto (fun i => iteratedFDeriv ℝ r
        (fun y => (gseq i).inner y (b a) (b c)) x) l
        (𝓝 (iteratedFDeriv ℝ r
          (fun y => g.inner y (b a) (b c)) x)))
    (hdefect : Tendsto (fun i => (Dseq i).negativeCurvaturePart x)
      l (𝓝 0)) :
    D.NonnegativeCurvatureOperator x := by
  classical
  obtain ⟨hzero, hone, htwo⟩ :=
    RiemannianMetric.tendsto_euclideanCoefficients_of_scalar_jets x b hjets
  have hinner (u v : EuclideanSpace ℝ (Fin 3)) :
      Tendsto (fun i => (gseq i).inner x u v) l (𝓝 (g.inner x u v)) := by
    have hu := (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp
      (hzero.prodMk_nhds (tendsto_const_nhds (x := u)))
    convert! (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp
      (hu.prodMk_nhds (tendsto_const_nhds (x := v))) using 1
  have hsource (i : alpha) (u v : EuclideanSpace ℝ (Fin 3)) :
      -(Dseq i).negativeCurvaturePart x ≤ (Dseq i).sectionalCurvature x u v := by
    have hnonneg : 0 ≤ (Dseq i).negativeCurvaturePart x := le_max_right _ _
    apply (Dseq i).sectionalCurvature_lower_bound_of_orthonormal x
      (neg_nonpos.mpr hnonneg) _ u v
    intro a c ha hc hac
    exact MetricSurgery.neg_negativeCurvaturePart_le_sectional_of_orthonormal
      (Dseq i) x ⟨ha, hc, hac⟩
  have hplane (u v : EuclideanSpace ℝ (Fin 3))
      (huv : LeviCivitaData.IsOrthonormalPair g x u v) :
      0 ≤ D.curvatureTensor x u v u v := by
    have hgram : Tendsto (fun i =>
        (gseq i).inner x u u * (gseq i).inner x v v -
          ((gseq i).inner x u v) ^ 2) l (𝓝 1) := by
      simpa only [huv.1, huv.2.1, huv.2.2, one_mul, zero_pow (by decide : 2 ≠ 0),
        sub_zero] using ((hinner u u).mul (hinner v v)).sub ((hinner u v).pow 2)
    have hR := LeviCivitaData.tendsto_curvatureTensor_of_metric_jets
      Dseq D x u v u v hzero hone htwo
    have hsec : Tendsto (fun i => (Dseq i).sectionalCurvature x u v) l
        (𝓝 (D.curvatureTensor x u v u v)) := by
      simpa only [LeviCivitaData.sectionalCurvature, Pi.div_def, div_one] using
        hR.div hgram (by norm_num : (1 : ℝ) ≠ 0)
    have hsum : Tendsto (fun i => (Dseq i).negativeCurvaturePart x +
        (Dseq i).sectionalCurvature x u v) l (𝓝 (D.curvatureTensor x u v u v)) := by
      simpa only [zero_add] using hdefect.add hsec
    exact ge_of_tendsto hsum (Eventually.of_forall fun i => by
      linarith only [hsource i u v])
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 3) : EuclideanSpace ℝ (Fin 3) → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨b3, _, _, hunit, hpair, _⟩ :=
    D.three_dimensional_curvature_operator_spectrum D.curvatureTensorCalculus x
  let W := fun u v : TangentSpace (𝓡 3) x =>
    (WithLp.toLp 2 (crossProduct (b3.repr u) (b3.repr v)) :
      EuclideanSpace ℝ (Fin 3))
  let L := Poincare.Geometry.Curvature.Operator.curvatureOperator
    (fun i j k m => D.curvatureTensor x (b3 i) (b3 j) (b3 k) (b3 m))
  change ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ = 1 →
    ∃ u v, LeviCivitaData.IsOrthonormalPair g x u v ∧ W u v = z at hunit
  change ∀ u v w z, D.curvatureTensor x u v w z =
    inner ℝ (W u v) (L (W w z)) at hpair
  have hLunit (z : EuclideanSpace ℝ (Fin 3)) (hz : ‖z‖ = 1) :
      0 ≤ inner ℝ z (L z) := by
    obtain ⟨u, v, huv, hW⟩ := hunit z hz
    have hp := hplane u v huv
    rw [hpair, hW] at hp
    exact hp
  have hL (z : EuclideanSpace ℝ (Fin 3)) : 0 ≤ inner ℝ z (L z) := by
    by_cases hz : z = 0
    · simp [hz]
    have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hp := hLunit (‖z‖⁻¹ • z) (norm_smul_inv_norm hz)
    rw [map_smul, real_inner_smul_left, real_inner_smul_right] at hp
    exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hnorm)).mp
      ((mul_nonneg_iff_of_pos_left (inv_pos.mpr hnorm)).mp hp)
  intro A _hA
  let e := g.orthonormalBasis x
  let Z : EuclideanSpace ℝ (Fin 3) := ∑ i, ∑ j, A i j • W (e i) (e j)
  have hquad : D.curvatureOperatorQuadratic x A = inner ℝ Z (L Z) := by
    change (∑ i, ∑ j, ∑ k, ∑ m,
      A i j * A k m * D.curvatureTensor x (e i) (e j) (e k) (e m)) = _
    simp_rw [Z, map_sum, map_smul, sum_inner, inner_sum,
      real_inner_smul_left, real_inner_smul_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hpair]
    ring
  rw [hquad]
  exact hL Z

end PoincareMT.M30
