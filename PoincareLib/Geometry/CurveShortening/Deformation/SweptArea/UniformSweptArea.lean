import PoincareLib.Geometry.CurveShortening.Deformation.SweptArea.InteriorSweptArea
import PoincareLib.Geometry.CurveShortening.Ramp.Estimates
import PoincareLib.Geometry.RicciFlow.CurveShortening.Integral.RegularizationError

/-!
# Uniform interior swept-area bounds for the retained family

Claim 19.23, Morgan--Tian pp. 453-454, using the preceding uniform family
bounds and corrected Corollary 19.10 (2015 correction pp. 7-9).
See M65 derivation 12.
-/

set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)} {G : M63AmbientGeometry F}
  {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))} {zeta : ℝ}

/-- One positive total-curvature bound chosen before the circumference and
family member; Claim 19.23, pp. 453-454, and corrected Corollary 19.10. -/
noncomputable def m65FamilyTotalCurvatureBound (C : M63FamilyConclusion G Gamma zeta) : ℝ :=
  2 * C.initial_bound * Real.exp (|m62C1 G.K0 G.K1 G.K2 + G.K2| * (b - a))

/-- Positivity of the retained uniform bound in Claim 19.23, pp. 453-454. -/
theorem m65FamilyTotalCurvatureBound_pos (C : M63FamilyConclusion G Gamma zeta) :
    0 < m65FamilyTotalCurvatureBound C := by
  unfold m65FamilyTotalCurvatureBound
  exact mul_pos (mul_pos (by norm_num) C.initial_bound_positive) (Real.exp_pos _)

/-- The actual total curvature is uniformly bounded over the full original
slab, all members and positive circumferences below one; Claim 19.23,
pp. 453-454. -/
theorem m65FamilyTotalCurvature_le (C : M63FamilyConclusion G Gamma zeta)
    {circumference : ℝ} (h : 0 < circumference) (hlt : circumference < 1)
    (z : LoopTwoSphere) {t : ℝ} (ht : t ∈ Set.Icc a b) :
    m62TotalCurvature (G.product circumference h).flow (C.solutions circumference h |>.curve z) t ≤
      m65FamilyTotalCurvatureBound C := by
  have hcoef : m63FamilyLengthSup (F.metric a) Gamma + 1 +
      (C.approximation.count : ℝ) * Real.pi ≤ 2 * C.initial_bound := by
    linarith [C.initial_length_bound, C.initial_turning_bound]
  have hexp : (m62C1 G.K0 G.K1 G.K2 + G.K2) * (t - a) ≤
      |m62C1 G.K0 G.K1 G.K2 + G.K2| * (b - a) :=
    mul_le_mul (le_abs_self _) (sub_le_sub_right ht.2 a)
      (sub_nonneg.mpr ht.1) (abs_nonneg _)
  have hlength := M62.length_nonneg (G.product circumference h).flow
    (C.solutions circumference h |>.curve z) t
  calc
    _ ≤ m62TotalCurvature (G.product circumference h).flow
        (C.solutions circumference h |>.curve z) t +
        m62Length (G.product circumference h).flow (C.solutions circumference h |>.curve z) t :=
      le_add_of_nonneg_right hlength
    _ ≤ _ := C.total_bound circumference h hlt z t ht
    _ ≤ (2 * C.initial_bound) *
        Real.exp ((m62C1 G.K0 G.K1 G.K2 + G.K2) * (t - a)) :=
      mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le
    _ ≤ m65FamilyTotalCurvatureBound C :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp)
        (mul_nonneg (by norm_num) C.initial_bound_positive.le)

/-- The genuine interior swept annulus satisfies a linear time bound with
constants independent of the circumference and member; Claim 19.23,
pp. 453-454. -/
theorem m65FamilyInteriorSweptAnnulus_area_le
    (C : M63FamilyConclusion G Gamma zeta)
    {circumference : ℝ} (h : 0 < circumference) (hlt : circumference < 1)
    (z : LoopTwoSphere) {s t q : ℝ} (has : a < s) (hst : s ≤ t) (htb : t < b)
    (hq : q ∈ Set.Icc a b) :
    (m65InteriorSweptAnnulus ((G.product circumference h).flow.metric q)
      ((C.solutions circumference h).shrinking z) has hst htb).area ≤
      Real.exp ((2 * G.K2) * (b - a)) * m65FamilyTotalCurvatureBound C * (t - s) := by
  let P := G.product circumference h
  let c := (C.solutions circumference h).curve z
  have hc := (C.solutions circumference h).shrinking z
  have hsub : Set.Icc s t ⊆ Set.Icc a b := fun _ hr =>
    ⟨has.le.trans hr.1, hr.2.trans htb.le⟩
  have hint : (∫ r in s..t, m62TotalCurvature P.flow c r) ≤
      m65FamilyTotalCurvatureBound C * (t - s) := by
    calc
      _ ≤ ∫ _r in s..t, m65FamilyTotalCurvatureBound C :=
        intervalIntegral.integral_mono_on hst
          (((M62.total_curvature_continuous P.flow c hc).mono hsub).intervalIntegrable_of_Icc hst)
          intervalIntegrable_const (fun r hr => m65FamilyTotalCurvature_le C h hlt z (hsub hr))
      _ = _ := by rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]; ring
  have harea := m65InteriorSweptAnnulus_area_le (G.product_bounds circumference h)
    G.nonnegative.2.2 hc has hst htb hq
  exact harea.trans ((mul_le_mul_of_nonneg_left hint (Real.exp_pos _).le).trans_eq (by ring))

end PoincareMT
