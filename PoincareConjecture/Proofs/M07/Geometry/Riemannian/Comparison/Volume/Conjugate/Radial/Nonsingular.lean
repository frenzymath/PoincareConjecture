import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.NoConjugate
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Radial.Jacobi
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Radial.Differential
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Radial.Domain

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RiemannianMetric

open ConnectionAlongCurve ConnectionVariation

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem isInvertible_mfderiv_of_minimizing_extension
    (g : RiemannianMetric n M) (D : LeviCivitaData g) {p : M} {R : ℝ}
    {e : EuclideanSpace ℝ (Fin n) → M}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R)) (he0 : e 0 = p)
    (hinit : (mfderiv (𝓡 n) (𝓡 n) e 0).IsInvertible)
    (hgeo : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun t : ℝ => e (t • v))
        {t : ℝ | t • v ∈ Metric.ball 0 R})
    (hspeed : ∀ v ∈ Metric.ball 0 R, ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (e (t • v))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e (s • v)) t 1) = ‖v‖)
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ Metric.ball 0 R) (hv0 : v ≠ 0)
    {q : ℝ} (hq : 1 < q) (hqR : q * ‖v‖ < R)
    (hmin : g.edist p (e (q • v)) = ENNReal.ofReal (q * ‖v‖)) :
    (mfderiv (𝓡 n) (𝓡 n) e v).IsInvertible := by
  apply isInvertible_mfderiv_of_injective
  apply (injective_iff_map_eq_zero _).mpr
  change ∀ w : EuclideanSpace ℝ (Fin n), mfderiv (𝓡 n) (𝓡 n) e v w = 0 → w = 0
  intro w hw
  by_contra hw0
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  let z := q • v
  have hz : z ∈ Metric.ball 0 R := by
    simpa only [z, Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg hq0.le]
      using hqR
  have hz0 : z ≠ 0 := smul_ne_zero hq0.ne' hv0
  let I : Set ℝ := {t : ℝ | t • z ∈ Metric.ball 0 R}
  let γ : ℝ → M := fun t => e (t • z)
  let J : (t : ℝ) → TangentSpace (𝓡 n) (γ t) :=
    fun t => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e (t • (z + s • w))) 0 1
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg v)
    (by simpa only [Metric.mem_ball, dist_zero_right] using hv)
  have hezero : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e 0 :=
    he.contMDiffAt (Metric.isOpen_ball.mem_nhds (by simpa using hR))
  have hI : IsOpen I := Metric.isOpen_ball.preimage (by fun_prop)
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ I := by
    apply he.comp
    · apply contMDiffOn_iff_contDiffOn.mpr
      fun_prop
    · exact fun _ ht => ht
  have hJ : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField γ (γ t) J) t := by
    intro t ht
    exact contDiffAt_chartField_radialVariation z w
      (he.contMDiffAt (Metric.isOpen_ball.mem_nhds ht)) (mem_extChartAt_source _)
  have hjac : ∀ t ∈ Icc (0 : ℝ) 1,
      manifoldCovDerivAlong g γ (manifoldCovDerivAlong g γ J 1) 1 t =
        -D.curvature (γ t) (J t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) := by
    intro t ht
    exact eq_neg_of_add_eq_zero_left (g.radialVariation_jacobi D he hgeo hz w ht)
  have hJ0 : J 0 = 0 := radialVariation_field_zero e z w
  have hDJ0 : manifoldCovDerivAlong g γ J 1 0 ≠ 0 := by
    rw [g.radialVariation_initial_covariantDerivative hezero z w]
    intro hzero
    apply hw0
    apply hinit.injective
    simpa only [map_zero] using hzero
  have hc : q⁻¹ ∈ Ioo (0 : ℝ) 1 :=
    ⟨inv_pos.mpr hq0, (inv_lt_one₀ hq0).mpr hq⟩
  obtain ⟨a, b, ha, hb, hab⟩ := exists_radial_closed_interval hz
  have hn := Conjugate.jacobi_ne_zero_of_minimizing g D ha hb hc hI hγ
    (hgeo z hz) hab hJ hjac hJ0 hDJ0 (norm_pos_iff.mpr hz0)
    (hspeed z hz) (by
      simpa only [γ, z, zero_smul, one_smul, he0, norm_smul,
        Real.norm_of_nonneg hq0.le] using hmin)
  apply hn
  have hcv : q⁻¹ • z = v := by
    dsimp only [z]
    rw [smul_smul, inv_mul_cancel₀ hq0.ne', one_smul]
  have hec : MDifferentiableAt (𝓡 n) (𝓡 n) e (q⁻¹ • z) := by
    rw [hcv]
    exact (he.contMDiffAt (Metric.isOpen_ball.mem_nhds hv)).mdifferentiableAt (by simp)
  have hfield := radialVariation_field_eq z w q⁻¹ hec
  change J q⁻¹ = mfderiv (𝓡 n) (𝓡 n) e (q⁻¹ • z) (q⁻¹ • w) at hfield
  rw [hfield, hcv, map_smul, hw, smul_zero]

end PoincareConjecture.RiemannianMetric
