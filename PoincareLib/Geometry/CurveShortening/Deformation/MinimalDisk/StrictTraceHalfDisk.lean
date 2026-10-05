import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.StrictTraceHarmonicPullback
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# Canonical differential traces on the actual closed half disk

The actual within differential supplies the continuous gradient and
connection coefficient consumed by the shared half-disk theorem.
The ordinary derivative is used only in the open interior.
Source: M65 derivation 43, actual boundary coordinate and matrix
equation, for Heinz 1970, pp. 99--105, and MT 19.2, pp. 438--439.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Complex Metric
open scoped Topology ContDiff

namespace PoincareMT.M65StrictTrace

open M65Branch

/-- The actual closed half disk has a dense open interior and unique
within differentials. Source: derivation 43, actual boundary domain. -/
theorem halfDisk_differential_domain {r : ℝ} (hr : 0 < r) :
    let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
    let U := ball (0 : ℂ) r ∩ {z | 0 < z.im}
    IsOpen U ∧ IsClosed K ∧ UniqueDiffOn ℝ K ∧ closure U = K := by
  let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
  let U := ball (0 : ℂ) r ∩ {z | 0 < z.im}
  have hU : IsOpen U := isOpen_ball.inter (isOpen_lt continuous_const continuous_im)
  have hK : IsClosed K := isClosed_closedBall.inter (isClosed_le continuous_const continuous_im)
  have hc : Convex ℝ K := (convex_closedBall (0 : ℂ) r).inter
    ((convex_Ici (0 : ℝ)).linear_preimage imCLM.toLinearMap)
  have hi : interior K = U := by
    dsimp [K, U]
    rw [interior_inter, interior_closedBall (0 : ℂ) hr.ne', interior_setOfPred_le_im]
  have hn : U.Nonempty := by
    refine ⟨((r / 2 : ℝ) : ℂ) * I, ?_, ?_⟩
    · rw [mem_ball_zero_iff, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hr)]
      linarith
    · change 0 < (((r / 2 : ℝ) : ℂ) * I).im
      simp only [mul_im, ofReal_re, ofReal_im, I_im, I_re, mul_one, zero_mul, add_zero]
      exact half_pos hr
  have hni : (interior K).Nonempty := hi.symm ▸ hn
  refine ⟨hU, hK, uniqueDiffOn_convex hc hni, ?_⟩
  change closure U = K
  rw [← hi, hc.closure_interior_eq_closure_of_nonempty_interior hni, hK.closure_eq]

/-- The literal within-differential complex gradient, defined also at
the diameter. Source: derivation 43, actual continuous boundary field. -/
def halfDiskGradient {n : ℕ} (H : ℂ → EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (z : ℂ) : Fin n → ℂ :=
  coordinateComplexification
    (fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im}) z 1) -
      I • coordinateComplexification
        (fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im}) z I)

/-- The connection matrix is formed from the actual within columns.
Source: derivation 43, continuous actual harmonic coefficient. -/
def halfDiskHarmonicMatrix {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (D : LeviCivitaData g) (H : ℂ → EuclideanSpace ℝ (Fin n)) (r : ℝ) (z : ℂ) :
    (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
  (-(2 : ℂ)⁻¹) •
    (complexifyOperator (M65Gauss.connectionCoefficient D (H z)
      (fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im}) z 1)) +
      I • complexifyOperator (M65Gauss.connectionCoefficient D (H z)
        (fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im}) z I)))

/-- The actual within gradient vanishes exactly when the entire actual
within differential vanishes. Source: derivation 43, actual branch set. -/
theorem halfDiskGradient_eq_zero_iff {n : ℕ}
    (H : ℂ → EuclideanSpace ℝ (Fin n)) (r : ℝ) (z : ℂ) :
    halfDiskGradient H r z = 0 ↔
      fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im}) z = 0 := by
  let T := fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im}) z
  simpa only [complexGradient, T.fderiv, T, halfDiskGradient] using
    complexGradient_eq_zero_iff T 0

/-- The open half disk is a genuine neighborhood within the closed
half disk. Source: derivation 43, actual derivative domain. -/
theorem halfDisk_mem_nhds {r : ℝ} {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) r ∩ {w | 0 < w.im}) :
    closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im} ∈ 𝓝 z := by
  apply mem_of_superset
    ((isOpen_ball.inter (isOpen_lt continuous_const continuous_im)).mem_nhds hz)
  intro w hw
  exact ⟨ball_subset_closedBall hw.1, (show 0 < w.im from hw.2).le⟩

/-- On the true interior, both canonical fields equal the ordinary
gradient and harmonic matrix. Source: derivation 43, actual traces. -/
theorem halfDisk_fields_eq {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (D : LeviCivitaData g) (H : ℂ → EuclideanSpace ℝ (Fin n)) {r : ℝ} {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) r ∩ {w | 0 < w.im}) :
    halfDiskGradient H r z = complexGradient H z ∧
      halfDiskHarmonicMatrix D H r z = harmonicMatrix D H z := by
  simp only [halfDiskGradient, halfDiskHarmonicMatrix,
    fderivWithin_of_mem_nhds (halfDisk_mem_nhds hz), complexGradient, harmonicMatrix,
    and_self]

/-- Actual within-C1 regularity supplies both continuous fields on
the entire closed half disk. Source: derivation 43, boundary matrix
equation; no ordinary derivative at the diameter is used. -/
theorem halfDisk_fields_continuousOn
    {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (D : LeviCivitaData g) {H : ℂ → EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hH : ContDiffOn ℝ 1 H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im})) :
    ContinuousOn (halfDiskGradient H r) (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}) ∧
      ContinuousOn (halfDiskHarmonicMatrix D H r)
        (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}) := by
  have hder := hH.continuousOn_fderivWithin (halfDisk_differential_domain hr).2.2.1 le_rfl
  have hc (v : ℂ) := hder.clm_apply (continuousOn_const (c := v))
  have hC := (M65Gauss.contDiff_connectionCoefficient D).continuous.comp_continuousOn
    hH.continuousOn
  constructor
  · exact (coordinateComplexification.continuous.comp_continuousOn (hc 1)).sub
      ((coordinateComplexification.continuous.comp_continuousOn (hc I)).const_smul I)
  · exact ((complexifyOperator.continuous.comp_continuousOn (hC.clm_apply (hc 1))).add
      ((complexifyOperator.continuous.comp_continuousOn
        (hC.clm_apply (hc I))).const_smul I)).const_smul
        (-(2 : ℂ)⁻¹)

/-- Genuine interior smoothness supplies the actual C1 fields and
their true matrix equation; the boundary remains the canonical within
trace. Source: derivation 43, shared half-disk inputs. -/
theorem halfDisk_fields_equation
    {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (D : LeviCivitaData g) {H : ℂ → EuclideanSpace ℝ (Fin n)} {r : ℝ}
    (hH : ContDiffOn ℝ ∞ H (ball (0 : ℂ) r ∩ {z | 0 < z.im}))
    (heq : ∀ z ∈ ball (0 : ℂ) r ∩ {w | 0 < w.im},
      dbar (complexGradient H) z = harmonicMatrix D H z (complexGradient H z)) :
    ContDiffOn ℝ 1 (halfDiskGradient H r) (ball (0 : ℂ) r ∩ {z | 0 < z.im}) ∧
      ContDiffOn ℝ 1 (halfDiskHarmonicMatrix D H r)
        (ball (0 : ℂ) r ∩ {z | 0 < z.im}) ∧
      ∀ z ∈ ball (0 : ℂ) r ∩ {w | 0 < w.im},
        dbar (halfDiskGradient H r) z =
          halfDiskHarmonicMatrix D H r z (halfDiskGradient H r z) := by
  have hU : IsOpen (ball (0 : ℂ) r ∩ {z | 0 < z.im}) :=
    isOpen_ball.inter (isOpen_lt continuous_const continuous_im)
  refine ⟨(contDiffOn_complexGradient hU hH).congr (fun z hz =>
      (halfDisk_fields_eq D H hz).1),
    (contDiffOn_harmonicMatrix D hU hH).congr (fun z hz =>
      (halfDisk_fields_eq D H hz).2), ?_⟩
  intro z hz
  have hfield : halfDiskGradient H r =ᶠ[𝓝 z] complexGradient H := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact (halfDisk_fields_eq D H hw).1
  rw [show dbar (halfDiskGradient H r) z = dbar (complexGradient H) z from
    congrArg dbarLinear hfield.fderiv_eq,
    (halfDisk_fields_eq D H hz).1, (halfDisk_fields_eq D H hz).2]
  exact heq z hz

end PoincareMT.M65StrictTrace
