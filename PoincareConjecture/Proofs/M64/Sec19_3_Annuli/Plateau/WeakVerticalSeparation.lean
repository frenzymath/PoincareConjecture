import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakReplacementIntegration
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.RectangleMeasurableIntegration
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.VariableModulusEnergy

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff BigOperators

namespace PoincareConjecture

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

namespace M64ObservedWeakAnnulus

theorem vertical_boundary_pairing_coordinate
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (hd : ContDiff ℝ 1 (fun x => e (c1 x) - e (c0 x))) (b : Fin m) :
    (∫ p in S, (e (c1 (p 0)) - e (c0 (p 0))) b * A.column 1 p b) =
      ∫ x in Icc (0 : ℝ) curvePeriod, ((e (c1 x) - e (c0 x)) b) ^ 2 := by
  let d : ℝ → E := fun x => e (c1 x) - e (c0 x)
  let phi : LoopPlane → ℝ := fun p => d (p 0) b
  have hd' : ContDiff ℝ 1 d := hd
  have hD : ContDiff ℝ 1 (fun p : LoopPlane => d (p 0)) :=
    hd.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff
  have hphi : ContDiff ℝ 1 phi := (EuclideanSpace.proj (𝕜 := ℝ) b).contDiff.comp hD
  have hpd (p : LoopPlane) :
      fderiv ℝ phi p (EuclideanSpace.single (1 : Fin 2) 1) = 0 := by
    have hfd := (hd'.differentiable (by simp) (p 0)).hasFDerivAt
    have hdp := hfd.comp p (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt
    have hh := (EuclideanSpace.proj (𝕜 := ℝ) b).hasFDerivAt.comp p hdp
    change HasFDerivAt phi _ p at hh
    rw [hh.fderiv]
    simp
  have hboundary := A.boundary phi hphi
  simp only [hpd, zero_smul, integral_zero, add_zero] at hboundary
  have hright : (fun x => phi (annulusPoint x 1) • e (c1 x) -
      phi (annulusPoint x 0) • e (c0 x)) = fun x => d x b • d x := by
    funext x
    simp [phi, d, annulusPoint, smul_sub]
  rw [hright] at hboundary
  have hli := m64L2_test_integrable (Lp.memLp (A.column 1))
    (m64Annulus_continuous_memLp_two hphi.continuous)
  have hri : IntegrableOn (fun x => d x b • d x) (Icc (0 : ℝ) curvePeriod) :=
    (((EuclideanSpace.proj (𝕜 := ℝ) b).continuous.comp hd'.continuous).smul
      hd'.continuous).integrableOn_Icc
  have hh := congrArg (EuclideanSpace.proj (𝕜 := ℝ) b) hboundary
  rw [← (EuclideanSpace.proj (𝕜 := ℝ) b).integral_comp_comm hli,
    ← (EuclideanSpace.proj (𝕜 := ℝ) b).integral_comp_comm hri] at hh
  simpa only [EuclideanSpace.coe_proj, Function.comp_apply, PiLp.smul_apply,
    smul_eq_mul, ← sq, phi, d] using hh

theorem boundary_coordinate_sq_le_vertical_column
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (hd : ContDiff ℝ 1 (fun x => e (c1 x) - e (c0 x))) (b : Fin m) :
    (∫ x in Icc (0 : ℝ) curvePeriod, ((e (c1 x) - e (c0 x)) b) ^ 2) ≤
      ∫ p in S, (A.column 1 p b) ^ 2 := by
  let d : ℝ → E := fun x => e (c1 x) - e (c0 x)
  let phi : LoopPlane → ℝ := fun p => d (p 0) b
  have hpc : Continuous phi :=
    (EuclideanSpace.proj (𝕜 := ℝ) b).continuous.comp
      (hd.continuous.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous)
  have hp : MemLp phi 2 mu := m64Annulus_continuous_memLp_two hpc
  have hv : MemLp (fun p => A.column 1 p b) 2 mu :=
    (EuclideanSpace.proj (𝕜 := ℝ) b).comp_memLp' (Lp.memLp (A.column 1))
  have hpsq := (memLp_two_iff_integrable_sq hp.aestronglyMeasurable).mp hp
  have hvsq := (memLp_two_iff_integrable_sq hv.aestronglyMeasurable).mp hv
  have hpair : Integrable (fun p => phi p * A.column 1 p b) mu := by
    simpa only [smul_eq_mul] using m64L2_test_integrable hv hp
  have hbase : (∫ p in S, phi p ^ 2) =
      ∫ x in Icc (0 : ℝ) curvePeriod, d x b ^ 2 := by
    have hiter := m64AnnulusInteriorIntegral_eq_iterated_integrable
      (fun p : LoopPlane => phi p ^ 2) hpsq
    calc
      _ = ∫ x in Icc (0 : ℝ) curvePeriod,
          ∫ s in Icc (0 : ℝ) 1, (phi (annulusPoint x s)) ^ 2 := hiter
      _ = _ := by simp [phi, d, annulusPoint]
  have hi := integral_mono (hpair.const_mul 2) (hpsq.add hvsq)
    (fun p => by
      change 2 * (phi p * A.column 1 p b) ≤ phi p ^ 2 + (A.column 1 p b) ^ 2
      nlinarith [sq_nonneg (phi p - A.column 1 p b)])
  have hi2 := hi
  rw [integral_const_mul] at hi2
  have hadd : (∫ p in S, (fun p => phi p ^ 2) p +
      (fun p => (A.column 1 p b) ^ 2) p) =
      (∫ p in S, phi p ^ 2) + ∫ p in S, (A.column 1 p b) ^ 2 := by
    simpa only [Pi.add_apply] using integral_add hpsq hvsq
  have hi' : 2 * (∫ p in S, phi p * A.column 1 p b) ≤
      (∫ p in S, phi p ^ 2) + ∫ p in S, (A.column 1 p b) ^ 2 :=
    hi2.trans_eq hadd
  rw [hbase] at hi'
  have hpairEq := A.vertical_boundary_pairing_coordinate hd b
  change (∫ p in S, phi p * A.column 1 p b) = ∫ x in Icc (0 : ℝ) curvePeriod, d x b ^ 2
    at hpairEq
  rw [hpairEq] at hi'
  change (∫ x in Icc (0 : ℝ) curvePeriod, d x b ^ 2) ≤ _
  linarith

theorem boundary_observed_sq_le_vertical_column
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (hd : ContDiff ℝ 1 (fun x => e (c1 x) - e (c0 x))) :
    (∫ x in Icc (0 : ℝ) curvePeriod, ‖e (c1 x) - e (c0 x)‖ ^ 2) ≤
      ∫ p in S, ‖A.column 1 p‖ ^ 2 := by
  have hleft (b : Fin m) : IntegrableOn (fun x => ((e (c1 x) - e (c0 x)) b) ^ 2)
      (Icc (0 : ℝ) curvePeriod) :=
    (((EuclideanSpace.proj (𝕜 := ℝ) b).continuous.comp hd.continuous).pow 2).integrableOn_Icc
  have hright (b : Fin m) : IntegrableOn (fun p => (A.column 1 p b) ^ 2) S := by
    have hv := (EuclideanSpace.proj (𝕜 := ℝ) b).comp_memLp' (Lp.memLp (A.column 1))
    exact (memLp_two_iff_integrable_sq hv.aestronglyMeasurable).mp hv
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum _ (fun b _ => hleft b),
    integral_finsetSum _ (fun b _ => hright b)]
  exact Finset.sum_le_sum fun b _ => A.boundary_coordinate_sq_le_vertical_column hd b

theorem weightedEnergy_ge_vertical_boundary
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    (hei : IsEmbedding e) {K : ℝ} (hK : ∀ q, ‖Q q‖ ≤ K)
    (hpos : ∀ q v, 0 ≤ Q q v v) {C : ℝ}
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * Q q v v)
    (hd : ContDiff ℝ 1 (fun x => e (c1 x) - e (c0 x)))
    {r : ℝ} (hr : 0 < r) :
    (r⁻¹ / (2 * max C 1)) *
        (∫ x in Icc (0 : ℝ) curvePeriod, ‖e (c1 x) - e (c0 x)‖ ^ 2) ≤
      A.weightedEnergy Q r := by
  let C' := max C 1
  have hC' : 0 < C' := by dsimp [C']; exact lt_max_of_lt_right zero_lt_one
  have hCnonneg : 0 ≤ C' := hC'.le
  have hcoercive' (q : M) (v : E)
      (hv : v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q)) :
      ‖v‖ ^ 2 ≤ C' * Q q v v := by
    exact (hcoercive q v hv).trans (mul_le_mul_of_nonneg_right
      (le_max_left C 1) (hpos q v))
  have hcolint : IntegrableOn (fun p => ‖A.column 1 p‖ ^ 2) S volume := by
    exact (memLp_two_iff_integrable_sq_norm
      (Lp.aestronglyMeasurable (A.column 1))).mp (Lp.memLp (A.column 1))
  have hqint := A.column_energy_integrable Q hQ hei hK 1
  have hcolle' : (∫ p in S, ‖A.column 1 p‖ ^ 2) ≤
      C' * ∫ p in S, Q (A.map p) (A.column 1 p) (A.column 1 p) := by
    have hae : ∀ᵐ p ∂volume.restrict S,
        ‖A.column 1 p‖ ^ 2 ≤ C' * Q (A.map p) (A.column 1 p) (A.column 1 p) := by
      filter_upwards [A.tangent 1] with p hp
      exact hcoercive' (A.map p) (A.column 1 p) hp
    have htmp := integral_mono_ae hcolint (hqint.const_mul C') hae
    rw [integral_const_mul] at htmp
    exact htmp
  have hboundary := A.boundary_observed_sq_le_vertical_column hd
  have hright : (r⁻¹ / (2 * C')) *
      (∫ x in Icc (0 : ℝ) curvePeriod, ‖e (c1 x) - e (c0 x)‖ ^ 2) ≤
      (r⁻¹ / 2) * ∫ p in S, Q (A.map p) (A.column 1 p) (A.column 1 p) := by
    calc
      _ ≤ (r⁻¹ / (2 * C')) * (∫ p in S, ‖A.column 1 p‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hboundary (by positivity)
      _ ≤ _ := by
        calc
          _ ≤ (r⁻¹ / (2 * C')) *
              (C' * ∫ p in S, Q (A.map p) (A.column 1 p) (A.column 1 p)) :=
            mul_le_mul_of_nonneg_left hcolle' (by positivity)
          _ = _ := by field_simp [hC'.ne', hr.ne']
  rw [A.weightedEnergy_eq_column_integrals Q hQ hei hK r]
  have hzero : 0 ≤ (r / 2) *
      (∫ p in S, Q (A.map p) (A.column 0 p) (A.column 0 p)) :=
    mul_nonneg (by positivity) (integral_nonneg fun p => hpos _ _)
  linarith

end M64ObservedWeakAnnulus

end PoincareConjecture
