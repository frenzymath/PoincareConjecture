import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.CompletedDerivativeBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.RepresentativeDerivative
import Mathlib.Analysis.InnerProductSpace.Dual









noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.HarmonicCoordinates

open LeviCivitaData.Dirichlet



theorem integral_fderiv_sq_le_of_smooth_representative
    {n : ℕ} {R a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (hell : ∀ x ∈ Metric.ball 0 R, ∀ v : EuclideanSpace ℝ (Fin n),
      a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
        g.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2)
    {Ω K S : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) (hΩR : Ω ⊆ Metric.ball 0 R)
    (hK : IsCompact K) (hΩK : Ω ⊆ K) (hS : IsCompact S) (hSΩ : S ⊆ Ω)
    (u : H1Zero D Ω) {U : EuclideanSpace ℝ (Fin n) → ℝ}
    (hUs : ContDiffOn ℝ ∞ U Ω)
    (hU : U =ᵐ[g.volumeMeasure.restrict Ω] (toL2 D Ω u : EuclideanSpace ℝ (Fin n) → ℝ)) :
    (∫ x in S, ‖fderiv ℝ U x‖ ^ 2) ≤
      (n : ℝ) * (b / Real.sqrt (a ^ n)) * ‖u‖ ^ 2 := by
  let e := OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin n))
  let P : Fin n → Lp ℝ 2 (volume.restrict Ω) := fun i =>
    localCoordinateDerivative e contMDiffOn_id contMDiffOn_id hK (by simp [e]) hΩK
      (EuclideanSpace.single i 1) u
  have hderiv (i : Fin n) : (P i : EuclideanSpace ℝ (Fin n) → ℝ)
      =ᵐ[volume.restrict Ω] fun x => fderiv ℝ U x (EuclideanSpace.single i 1) :=
    localCoordinateDerivative_id_eq_fderiv_ae hK hΩK hΩ subset_rfl u hUs hU i
  have hcoord (i : Fin n) :
      (∫ x in S, (fderiv ℝ U x (EuclideanSpace.single i 1)) ^ 2) ≤
        (b / Real.sqrt (a ^ n)) * ‖u‖ ^ 2 := by
    have hp : (∫ x in Ω, (P i x) ^ 2) = ‖P i‖ ^ 2 := by
      simpa only [Lp.toLp_coeFn] using
        (Poincare.Analysis.Sobolev.norm_toLp_sq_eq_integral (Lp.memLp (P i))).symm
    have hsmall := (hderiv i).filter_mono
      (ae_mono (Measure.restrict_mono hSΩ (le_refl volume)))
    calc
      _ = ∫ x in S, (P i x) ^ 2 := by
        apply integral_congr_ae
        filter_upwards [hsmall] with x hx
        exact congrArg (fun t : ℝ => t ^ 2) hx.symm
      _ ≤ ∫ x in Ω, (P i x) ^ 2 :=
        setIntegral_mono_set (Lp.memLp (P i)).integrable_sq
          (Eventually.of_forall fun x => sq_nonneg _) (Eventually.of_forall hSΩ)
      _ = ‖P i‖ ^ 2 := hp
      _ ≤ _ := by
        simpa only [PiLp.norm_single, norm_one, one_pow, mul_one] using
          localCoordinateDerivative_refl_norm_sq_le_of_ellipticity ha hb D hell hΩR hK hΩK
            (EuclideanSpace.single i 1) u
  have hpoint (x : EuclideanSpace ℝ (Fin n)) : ‖fderiv ℝ U x‖ ^ 2 =
      ∑ i, (fderiv ℝ U x (EuclideanSpace.single i 1)) ^ 2 := by
    simpa only [EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).norm_dual (fderiv ℝ U x)
  have hi (i : Fin n) : IntegrableOn
      (fun x => (fderiv ℝ U x (EuclideanSpace.single i 1)) ^ 2) S :=
    ((((hUs.continuousOn_fderiv_of_isOpen hΩ (by simp)).clm_apply
      continuousOn_const).pow 2).mono hSΩ).integrableOn_compact hS
  simp_rw [hpoint]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  calc
    _ ≤ ∑ _i : Fin n, (b / Real.sqrt (a ^ n)) * ‖u‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => hcoord i
    _ = _ := by simp [mul_assoc]



theorem integral_fderiv_sq_le_of_smooth_linear_replacement
    {n : ℕ} {R a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (hell : ∀ x ∈ Metric.ball 0 R, ∀ v : EuclideanSpace ℝ (Fin n),
      a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
        g.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2)
    {Ω K S : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) (hΩR : Ω ⊆ Metric.ball 0 R)
    (hK : IsCompact K) (hΩK : Ω ⊆ K) (hS : IsCompact S) (hSΩ : S ⊆ Ω)
    (u : H1Zero D Ω) (ℓ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    {U : EuclideanSpace ℝ (Fin n) → ℝ} (hUs : ContDiffOn ℝ ∞ U Ω)
    (hU : U =ᵐ[g.volumeMeasure.restrict Ω]
      fun x => ℓ x + (toL2 D Ω u) x) :
    (∫ x in S, ‖fderiv ℝ U x‖ ^ 2) ≤
      2 * volume.real S * ‖ℓ‖ ^ 2 +
        2 * ((n : ℝ) * (b / Real.sqrt (a ^ n)) * ‖u‖ ^ 2) := by
  let V := fun x => U x - ℓ x
  have hVs : ContDiffOn ℝ ∞ V Ω := hUs.sub ℓ.contDiff.contDiffOn
  have hV : V =ᵐ[g.volumeMeasure.restrict Ω]
      (toL2 D Ω u : EuclideanSpace ℝ (Fin n) → ℝ) := by
    filter_upwards [hU] with x hx
    simp only [V, hx, add_sub_cancel_left]
  have henergy := integral_fderiv_sq_le_of_smooth_representative ha hb D hell
    hΩ hΩR hK hΩK hS hSΩ u hVs hV
  have hUi : IntegrableOn (fun x => ‖fderiv ℝ U x‖ ^ 2) S :=
    (((hUs.continuousOn_fderiv_of_isOpen hΩ (by simp)).norm.pow 2).mono hSΩ).integrableOn_compact hS
  have hVi : IntegrableOn (fun x => ‖fderiv ℝ V x‖ ^ 2) S :=
    (((hVs.continuousOn_fderiv_of_isOpen hΩ (by simp)).norm.pow 2).mono hSΩ).integrableOn_compact hS
  have hconst : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin n) => 2 * ‖ℓ‖ ^ 2) S :=
    integrableOn_const hS.measure_lt_top.ne
  have hpoint : (∫ x in S, ‖fderiv ℝ U x‖ ^ 2) ≤
      ∫ x in S, 2 * ‖fderiv ℝ V x‖ ^ 2 + 2 * ‖ℓ‖ ^ 2 := by
    apply setIntegral_mono_on hUi ((hVi.const_mul 2).add hconst) hS.measurableSet
    intro x hx
    change ‖fderiv ℝ U x‖ ^ 2 ≤ 2 * ‖fderiv ℝ V x‖ ^ 2 + 2 * ‖ℓ‖ ^ 2
    have hd : fderiv ℝ V x = fderiv ℝ U x - ℓ := by
      exact (fderiv_sub
        ((hUs.contDiffAt (hΩ.mem_nhds (hSΩ hx))).differentiableAt (by simp))
        ℓ.differentiableAt).trans (by rw [ℓ.fderiv])
    have heq : fderiv ℝ U x = fderiv ℝ V x + ℓ := by rw [hd]; abel
    have hnorm : ‖fderiv ℝ U x‖ ≤ ‖fderiv ℝ V x‖ + ‖ℓ‖ := by
      rw [heq]
      exact norm_add_le _ _
    have hs := (sq_le_sq₀ (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hnorm
    nlinarith only [hs, sq_nonneg (‖fderiv ℝ V x‖ - ‖ℓ‖)]
  rw [integral_add (hVi.const_mul 2) hconst, integral_const_mul,
    setIntegral_const, smul_eq_mul] at hpoint
  nlinarith only [hpoint, henergy]

end PoincareConjecture.HarmonicCoordinates
