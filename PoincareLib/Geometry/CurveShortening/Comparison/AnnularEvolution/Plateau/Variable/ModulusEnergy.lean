import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Weak.AnnulusClass

/-!
# Actual weak annular energy at variable cylinder modulus

The two source columns carry the reciprocal positive weights `r` and
`r^-1`. On a compact positive modulus interval these energies control
the fixed-modulus energy uniformly, supplying genuine weak compactness.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareMT.M64ObservedWeakAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain

/-- The genuine observed Dirichlet energy for cylinder modulus `r`. Source: Morgan-Tian
Lemma 19.15, pp. 447-449; M64 derivation `2026-09-26-raw-harmonic-stress.md`. -/
def weightedEnergy (B : M → E →L[ℝ] E →L[ℝ] ℝ) (r : ℝ)
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1) : ℝ :=
  ∫ p in S, (r * B (A.map p) (A.column 0 p) (A.column 0 p) +
    r⁻¹ * B (A.map p) (A.column 1 p) (A.column 1 p)) / 2

/-- Positive modulus gives nonnegative actual weighted energy. Source: Morgan-Tian Lemma
19.15, pp. 447-449; M64 derivation `2026-09-26-raw-harmonic-stress.md`. -/
theorem weightedEnergy_nonneg (B : M → E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ q v, 0 ≤ B q v v) {r : ℝ} (hr : 0 ≤ r)
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1) : 0 ≤ A.weightedEnergy B r :=
  integral_nonneg fun p => div_nonneg
    (add_nonneg (mul_nonneg hr (hpos _ _))
      (mul_nonneg (inv_nonneg.mpr hr) (hpos _ _))) (by norm_num)

/-- The weighted density is integrable for every finite real modulus. Source: Morgan-Tian
Lemma 19.15, pp. 447-449; M64 derivation `2026-09-26-raw-harmonic-stress.md`. -/
theorem weightedEnergy_integrable (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    (hei : IsEmbedding e) {K : ℝ} (hb : ∀ q, ‖B q‖ ≤ K)
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1) (r : ℝ) :
    IntegrableOn (fun p => (r * B (A.map p) (A.column 0 p) (A.column 0 p) +
      r⁻¹ * B (A.map p) (A.column 1 p) (A.column 1 p)) / 2) S volume :=
  (((A.column_energy_integrable B hB hei hb 0).const_mul r).add
    ((A.column_energy_integrable B hB hei hb 1).const_mul r⁻¹)).div_const 2

/-- Integrable weighted energy is the sum of the two weighted column integrals. Source:
Morgan-Tian Lemma 19.15, pp. 447-449; M64 derivation `2026-09-26-raw-harmonic-stress.md`. -/
theorem weightedEnergy_eq_column_integrals
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    (hei : IsEmbedding e) {K : ℝ} (hb : ∀ q, ‖B q‖ ≤ K)
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1) (r : ℝ) :
    A.weightedEnergy B r =
      (r / 2) * (∫ p in S, B (A.map p) (A.column 0 p) (A.column 0 p)) +
      (r⁻¹ / 2) * (∫ p in S, B (A.map p) (A.column 1 p) (A.column 1 p)) := by
  rw [weightedEnergy, integral_div, integral_add
    ((A.column_energy_integrable B hB hei hb 0).const_mul r)
    ((A.column_energy_integrable B hB hei hb 1).const_mul r⁻¹),
    integral_const_mul, integral_const_mul]
  ring

/-- A bounded observed quadratic form controls each actual column energy by the squared L2
norm. Source: Morgan-Tian Lemma 19.15, pp. 447-449; M64 derivation
`2026-09-26-raw-harmonic-stress.md`. -/
theorem column_energy_le_norm_sq
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    (hei : IsEmbedding e) {K : ℝ} (hb : ∀ q, ‖B q‖ ≤ K)
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1) (i : Fin 2) :
    (∫ p in S, B (A.map p) (A.column i p) (A.column i p)) ≤ K * ‖A.column i‖ ^ 2 := by
  have hi := (memLp_two_iff_integrable_sq_norm
    (Lp.aestronglyMeasurable (A.column i))).mp (Lp.memLp (A.column i))
  calc
    _ ≤ ∫ p in S, K * ‖A.column i p‖ ^ 2 := by
      apply integral_mono_ae (A.column_energy_integrable B hB hei hb i) (hi.const_mul K)
      exact Eventually.of_forall fun p => by
        have hop := (B (A.map p)).le_opNorm₂ (A.column i p) (A.column i p)
        have hh := mul_le_mul_of_nonneg_right (hb (A.map p)) (sq_nonneg ‖A.column i p‖)
        rw [Real.norm_eq_abs] at hop
        nlinarith [le_abs_self (B (A.map p) (A.column i p) (A.column i p))]
    _ = _ := by rw [integral_const_mul, ← LpFiniteCoordinatesNative.l2_norm_sq]

/-- Moduli in a compact positive interval control the unweighted energy with the uniform
factor `max (lo^-1) hi`. Source: Morgan-Tian Lemma 19.15, pp. 447-449; M64 derivation
`2026-09-26-raw-harmonic-stress.md`. -/
theorem energy_le_weightedEnergy_of_mem
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    (hei : IsEmbedding e) {K : ℝ} (hb : ∀ q, ‖B q‖ ≤ K)
    (hpos : ∀ q v, 0 ≤ B q v v) {lo hi r : ℝ} (hlo : 0 < lo) (hr : r ∈ Icc lo hi)
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1) :
    A.energy B ≤ max lo⁻¹ hi * A.weightedEnergy B r := by
  have hrpos : 0 < r := hlo.trans_le hr.1
  have h0 : 1 ≤ max lo⁻¹ hi * r := by
    have hh := mul_le_mul_of_nonneg_left hr.1 (inv_nonneg.mpr hlo.le)
    rw [inv_mul_cancel₀ hlo.ne'] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hrpos.le)
  have h1 : 1 ≤ max lo⁻¹ hi * r⁻¹ := by
    have hh := mul_le_mul_of_nonneg_right (hr.2.trans (le_max_right lo⁻¹ hi))
      (inv_nonneg.mpr hrpos.le)
    simpa only [mul_inv_cancel₀ hrpos.ne'] using hh
  calc
    _ ≤ ∫ p in S, max lo⁻¹ hi *
        ((r * B (A.map p) (A.column 0 p) (A.column 0 p) +
          r⁻¹ * B (A.map p) (A.column 1 p) (A.column 1 p)) / 2) := by
      apply integral_mono_ae (A.energy_integrable B hB hei hb)
        ((A.weightedEnergy_integrable B hB hei hb r).const_mul _)
      exact Eventually.of_forall fun p => by
        have hh0 := mul_le_mul_of_nonneg_right h0 (hpos (A.map p) (A.column 0 p))
        have hh1 := mul_le_mul_of_nonneg_right h1 (hpos (A.map p) (A.column 1 p))
        nlinarith
    _ = _ := integral_const_mul _ _

end PoincareMT.M64ObservedWeakAnnulus
