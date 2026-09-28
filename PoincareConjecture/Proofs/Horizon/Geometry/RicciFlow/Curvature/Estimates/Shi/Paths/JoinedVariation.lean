import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic













set_option autoImplicit false

open Filter Set Topology
open scoped ContDiff

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

noncomputable def quadraticPathJet
    (x : V) (A : V →L[ℝ] V) (B : V →L[ℝ] V →L[ℝ] V)
    (z : V) : V :=
  x + A z + (1 / 2 : ℝ) • B z z

noncomputable def joinedCoordinateVariation
    (a b : ℝ) (x : ℝ → V)
    (A : ℝ → V →L[ℝ] V)
    (B : ℝ → V →L[ℝ] V →L[ℝ] V)
    (left right : V → V) (t : ℝ) (z : V) : V :=
  quadraticPathJet (x t) (A t) (B t) z +
    ((b - t) / (b - a)) •
      (left z - quadraticPathJet (x a) (A a) (B a) z) +
    ((t - a) / (b - a)) •
      (right z - quadraticPathJet (x b) (A b) (B b) z)

private theorem contDiff_quadraticPathJet
    (x : V) (A : V →L[ℝ] V) (B : V →L[ℝ] V →L[ℝ] V) :
    ContDiff ℝ ∞ (quadraticPathJet x A B) := by
  have hx : ContDiff ℝ ∞ (fun _ : V => x) := contDiff_const
  simpa +instances only [quadraticPathJet, Pi.add_apply, Pi.smul_apply] using!
    (hx.add A.contDiff).add
    ((B.contDiff.clm_apply contDiff_id).const_smul (1 / 2 : ℝ))

set_option backward.isDefEq.respectTransparency false in
private theorem hasFDerivAt_quadraticPathJet
    (x : V) (A : V →L[ℝ] V) (B : V →L[ℝ] V →L[ℝ] V)
    (hB : ∀ v w, B v w = B w v) (z : V) :
    HasFDerivAt (quadraticPathJet x A B) (A + B z) z := by
  have hd := (B.hasFDerivAt_of_bilinear
    (hasFDerivAt_id z) (hasFDerivAt_id z)).const_smul (1 / 2 : ℝ)
  have heq : (1 / 2 : ℝ) •
      (B.precompR V z (ContinuousLinearMap.id ℝ V) +
        B.precompL V (ContinuousLinearMap.id ℝ V) z) = B z := by
    ext v : 1
    change (1 / 2 : ℝ) • (B z v + B v z) = B z v
    rw [hB v z]
    module
  simp only [id_eq] at hd
  rw [heq] at hd
  simpa +instances only [quadraticPathJet, Pi.add_apply, Pi.smul_apply, zero_add] using!
    ((hasFDerivAt_const x z).add A.hasFDerivAt).add hd

set_option backward.isDefEq.respectTransparency false in
theorem joinedCoordinateVariation_endpoint_jets
    (a b : ℝ) (hab : a < b) (ρ : ℝ) (hρ : 0 < ρ)
    (x : ℝ → V) (A : ℝ → V →L[ℝ] V)
    (B : ℝ → V →L[ℝ] V →L[ℝ] V)
    (left right : V → V)
    (hB : ∀ t v w, B t v w = B t w v)
    (hleft : ContDiffOn ℝ ∞ left (Metric.ball 0 ρ))
    (hright : ContDiffOn ℝ ∞ right (Metric.ball 0 ρ))
    (hl0 : left 0 = x a)
    (hl1 : fderiv ℝ left 0 = A a)
    (hl2 : fderiv ℝ (fderiv ℝ left) 0 = B a)
    (hr0 : right 0 = x b)
    (hr1 : fderiv ℝ right 0 = A b)
    (hr2 : fderiv ℝ (fderiv ℝ right) 0 = B b) :
    joinedCoordinateVariation a b x A B left right a = left ∧
    joinedCoordinateVariation a b x A B left right b = right ∧
    ∀ t,
      ContDiffOn ℝ ∞ (joinedCoordinateVariation a b x A B left right t)
        (Metric.ball 0 ρ) ∧
      joinedCoordinateVariation a b x A B left right t 0 = x t ∧
      fderiv ℝ (joinedCoordinateVariation a b x A B left right t) 0 = A t ∧
      fderiv ℝ (fderiv ℝ
        (joinedCoordinateVariation a b x A B left right t)) 0 = B t := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
  refine ⟨?_, ?_, ?_⟩
  · funext z
    simp only [joinedCoordinateVariation, sub_self, div_self hba, one_smul,
      zero_div, zero_smul]
    abel
  · funext z
    simp only [joinedCoordinateVariation, sub_self, div_self hba, one_smul,
      zero_div, zero_smul]
    abel
  · intro t
    have hlDiff (z : V) (hz : z ∈ Metric.ball 0 ρ) :
        DifferentiableAt ℝ left z :=
      (hleft.contDiffAt (Metric.isOpen_ball.mem_nhds hz)).differentiableAt (by simp)
    have hrDiff (z : V) (hz : z ∈ Metric.ball 0 ρ) :
        DifferentiableAt ℝ right z :=
      (hright.contDiffAt (Metric.isOpen_ball.mem_nhds hz)).differentiableAt (by simp)
    have horder : (1 : ℕ∞ω) + 1 ≤ ∞ := by
      norm_num; exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
    have hlD2 : HasFDerivAt (fderiv ℝ left) (B a) (0 : V) := by
      have h := ((hleft.contDiffAt (Metric.ball_mem_nhds 0 hρ)).fderiv_right
        (m := 1) horder).differentiableAt (by norm_num)
      simpa +instances only [hl2] using! h.hasFDerivAt
    have hrD2 : HasFDerivAt (fderiv ℝ right) (B b) (0 : V) := by
      have h := ((hright.contDiffAt (Metric.ball_mem_nhds 0 hρ)).fderiv_right
        (m := 1) horder).differentiableAt (by norm_num)
      simpa +instances only [hr2] using! h.hasFDerivAt
    let L : V → V →L[ℝ] V := fun z =>
      A t + B t z + ((b - t) / (b - a)) •
        (fderiv ℝ left z - (A a + B a z)) +
      ((t - a) / (b - a)) • (fderiv ℝ right z - (A b + B b z))
    have hF (z : V) (hz : z ∈ Metric.ball 0 ρ) :
        fderiv ℝ (joinedCoordinateVariation a b x A B left right t) z = L z := by
      exact (((hasFDerivAt_quadraticPathJet (x t) (A t) (B t) (hB t) z).add
        (((hlDiff z hz).hasFDerivAt.sub
          (hasFDerivAt_quadraticPathJet (x a) (A a) (B a) (hB a) z)).const_smul
            ((b - t) / (b - a)))).add
        (((hrDiff z hz).hasFDerivAt.sub
          (hasFDerivAt_quadraticPathJet (x b) (A b) (B b) (hB b) z)).const_smul
            ((t - a) / (b - a)))).fderiv
    have hbase (s : ℝ) :
        HasFDerivAt (fun z : V => A s + B s z) (B s) (0 : V) :=
      (B s).hasFDerivAt.const_add (A s)
    have hLD : HasFDerivAt L (B t) (0 : V) := by
      simpa +instances only [L, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
        sub_self, smul_zero, add_zero] using!
        (((hbase t).add ((hlD2.sub (hbase a)).const_smul ((b - t) / (b - a)))).add
          ((hrD2.sub (hbase b)).const_smul ((t - a) / (b - a))))
    have hFeq :
        fderiv ℝ (joinedCoordinateVariation a b x A B left right t) =ᶠ[𝓝 0] L := by
      filter_upwards [Metric.ball_mem_nhds 0 hρ] with z hz
      exact hF z hz
    refine ⟨?_, ?_, ?_, (hLD.congr_of_eventuallyEq hFeq).fderiv⟩
    · have hqcont (s : ℝ) : ContDiffOn ℝ ∞
          (quadraticPathJet (x s) (A s) (B s)) (Metric.ball 0 ρ) :=
        (contDiff_quadraticPathJet (x s) (A s) (B s)).contDiffOn
      simpa +instances only [joinedCoordinateVariation, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply] using!
        (((hqcont t).add ((hleft.sub (hqcont a)).const_smul
          ((b - t) / (b - a)))).add ((hright.sub (hqcont b)).const_smul
            ((t - a) / (b - a))))
    · simp [joinedCoordinateVariation, quadraticPathJet, hl0, hr0]
    · simpa only [L, map_zero, add_zero, hl1, hr1, sub_self, smul_zero] using
        hF 0 (Metric.mem_ball_self hρ)

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivWithinAt_joinedCoordinateVariation
    (a b t : ℝ) (z : V)
    (x : ℝ → V) (A : ℝ → V →L[ℝ] V)
    (B : ℝ → V →L[ℝ] V →L[ℝ] V)
    (left right : V → V)
    (X : V) (A1 : V →L[ℝ] V) (B1 : V →L[ℝ] V →L[ℝ] V)
    (hx : HasDerivWithinAt x X (Icc a b) t)
    (hA : HasDerivWithinAt A A1 (Icc a b) t)
    (hB : HasDerivWithinAt B B1 (Icc a b) t) :
    HasDerivWithinAt
      (fun s => joinedCoordinateVariation a b x A B left right s z)
      (X + A1 z + (1 / 2 : ℝ) • B1 z z + (b - a)⁻¹ •
        ((right z - quadraticPathJet (x b) (A b) (B b) z) -
          (left z - quadraticPathJet (x a) (A a) (B a) z)))
      (Icc a b) t := by
  have hAz : HasDerivWithinAt (fun s => A s z) (A1 z) (Icc a b) t := by
    simpa only [map_zero, add_zero] using
      hA.clm_apply (hasDerivWithinAt_const t (Icc a b) z)
  have hBz : HasDerivWithinAt (fun s => B s z z) (B1 z z) (Icc a b) t := by
    simpa only [map_zero, add_zero] using
      (hB.clm_apply (hasDerivWithinAt_const t (Icc a b) z)).clm_apply
        (hasDerivWithinAt_const t (Icc a b) z)
  have hq : HasDerivWithinAt
      (fun s => quadraticPathJet (x s) (A s) (B s) z)
      (X + A1 z + (1 / 2 : ℝ) • B1 z z) (Icc a b) t := by
    simpa +instances only [quadraticPathJet, Pi.add_apply, Pi.smul_apply] using!
      HasDerivWithinAt.add (HasDerivWithinAt.add hx hAz)
        (hBz.const_smul (1 / 2 : ℝ))
  have hla : HasDerivWithinAt (fun s : ℝ => (b - s) / (b - a))
      (-(b - a)⁻¹) (Icc a b) t := by
    simpa +instances only [Pi.sub_apply, id_eq, zero_sub, neg_div, one_div] using!
      (HasDerivWithinAt.sub (hasDerivWithinAt_const t (Icc a b) b)
        (hasDerivWithinAt_id t (Icc a b))).div_const (b - a)
  have hra : HasDerivWithinAt (fun s : ℝ => (s - a) / (b - a))
      (b - a)⁻¹ (Icc a b) t := by
    simpa +instances only [Pi.sub_apply, id_eq, sub_zero, one_div] using!
      (HasDerivWithinAt.sub (hasDerivWithinAt_id t (Icc a b))
        (hasDerivWithinAt_const t (Icc a b) a)).div_const (b - a)
  have hd := HasDerivWithinAt.add (HasDerivWithinAt.add hq (hla.smul_const
    (left z - quadraticPathJet (x a) (A a) (B a) z)))
      (hra.smul_const (right z - quadraticPathJet (x b) (A b) (B b) z))
  have heq : X + A1 z + (1 / 2 : ℝ) • B1 z z +
      (-(b - a)⁻¹) • (left z - quadraticPathJet (x a) (A a) (B a) z) +
      (b - a)⁻¹ • (right z - quadraticPathJet (x b) (A b) (B b) z) =
      X + A1 z + (1 / 2 : ℝ) • B1 z z + (b - a)⁻¹ •
        ((right z - quadraticPathJet (x b) (A b) (B b) z) -
          (left z - quadraticPathJet (x a) (A a) (B a) z)) := by
    module
  simpa +instances only [joinedCoordinateVariation, Pi.add_apply] using!
    hd.congr_deriv heq

end PoincareConjecture.RicciFlowAnalysis
