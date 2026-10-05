import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Weak.AnnulusClass
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Sequences

/-!
# Actual almost-everywhere selection of monotone boundary labels

Countable compact product selection on rational arguments, followed by
monotone squeezing at continuity points, gives the Helly subsequence.
The exceptional set is countable. This is the label-selection step in
the free-boundary Douglas--Morrey direct method for MT2007 Lemma 19.15.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareMT.M64

/-- Pointwise bounded monotone real functions have an actual subsequence converging almost
everywhere to a monotone function. The literal liminf identity permits exact affine-period
rules to pass to the limit later. Source: Morgan-Tian Lemma 19.15, pp. 447-449; M64
derivation `2026-09-25-free-label-compactness.md`. -/
theorem monotone_sequence_subsequence_ae
    (f : ℕ → ℝ → ℝ) (hmono : ∀ j, Monotone (f j))
    (hbounded : ∀ x : ℝ, ∃ lo hi : ℝ, ∀ j, f j x ∈ Icc lo hi) :
    ∃ (k : ℕ → ℕ) (L : ℝ → ℝ), StrictMono k ∧ Monotone L ∧
      (∀ x, L x = liminf (fun j => f (k j) x) atTop) ∧
      (∀ x, ContinuousAt L x → Tendsto (fun j => f (k j) x) atTop (𝓝 (L x))) ∧
      ∀ᵐ x ∂volume, Tendsto (fun j => f (k j) x) atTop (𝓝 (L x)) := by
  classical
  choose lo hi hb using hbounded
  let X := (q : ℚ) → Icc (lo q) (hi q)
  let v : ℕ → X := fun j q => ⟨f j q, hb q j⟩
  obtain ⟨w, k, hk, hw⟩ := CompactSpace.tendsto_subseq v
  let L : ℝ → ℝ := fun x => liminf (fun j => f (k j) x) atTop
  have hbelow (x : ℝ) : IsBoundedUnder (· ≥ ·) atTop (fun j => f (k j) x) :=
    isBoundedUnder_of ⟨lo x, fun j => (hb x (k j)).1⟩
  have habove (x : ℝ) : IsBoundedUnder (· ≤ ·) atTop (fun j => f (k j) x) :=
    isBoundedUnder_of ⟨hi x, fun j => (hb x (k j)).2⟩
  have hL : Monotone L := by
    intro x y hxy
    exact liminf_le_liminf (Eventually.of_forall fun j => hmono (k j) hxy)
      (hbelow x) (habove y).isCobounded_ge
  have hrat (q : ℚ) : Tendsto (fun j => f (k j) q) atTop (𝓝 (L q)) := by
    have hq : Tendsto (fun j => f (k j) q) atTop (𝓝 ((w q : Icc (lo q) (hi q)) : ℝ)) :=
      (continuous_subtype_val.tendsto (w q)).comp ((tendsto_pi_nhds.mp hw) q)
    have hlim : L q = (w q : ℝ) := hq.liminf_eq
    rwa [hlim]
  have hconverges (x : ℝ) (hc : ContinuousAt L x) :
      Tendsto (fun j => f (k j) x) atTop (𝓝 (L x)) := by
    apply tendsto_order.mpr
    constructor
    · intro y hy
      obtain ⟨l, u, ⟨hl, hu⟩, hsub⟩ :=
        mem_nhds_iff_exists_Ioo_subset.mp (hc (Ioi_mem_nhds hy))
      obtain ⟨q, hlq, hqx⟩ := exists_rat_btwn hl
      have hyq : y < L q := hsub ⟨hlq, hqx.trans hu⟩
      filter_upwards [(hrat q) (Ioi_mem_nhds hyq)] with j hj
      exact hj.trans_le (hmono (k j) hqx.le)
    · intro y hy
      obtain ⟨l, u, ⟨hl, hu⟩, hsub⟩ :=
        mem_nhds_iff_exists_Ioo_subset.mp (hc (Iio_mem_nhds hy))
      obtain ⟨q, hxq, hqu⟩ := exists_rat_btwn hu
      have hqy : L q < y := hsub ⟨hl.trans hxq, hqu⟩
      filter_upwards [(hrat q) (Iio_mem_nhds hqy)] with j hj
      exact (hmono (k j) hxq.le).trans_lt hj
  refine ⟨k, L, hk, hL, fun _ => rfl, hconverges, ?_⟩
  have hcontinuous : ∀ᵐ x ∂volume, ContinuousAt L x := by
    rw [ae_iff]
    exact hL.countable_not_continuousAt.measure_zero volume
  filter_upwards [hcontinuous] with x hx
  exact hconverges x hx

/-- An actual affine-period rule passes through the bounded liminf, even before continuity
of the selected monotone limit is known. Source: Morgan-Tian Lemma 19.15, pp. 447-449; M64
derivation `2026-09-25-free-label-compactness.md`. -/
theorem liminf_period_shift
    (f : ℕ → ℝ → ℝ) {P : ℝ}
    (hperiod : ∀ j x, f j (x + P) = f j x + P)
    (hbounded : ∀ x : ℝ, ∃ lo hi : ℝ, ∀ j, f j x ∈ Icc lo hi) :
    ∀ x, liminf (fun j => f j (x + P)) atTop =
      liminf (fun j => f j x) atTop + P := by
  intro x
  obtain ⟨lo, hi, hb⟩ := hbounded x
  have hbelow : IsBoundedUnder (· ≥ ·) atTop (fun j => f j x) :=
    isBoundedUnder_of ⟨lo, fun j => (hb j).1⟩
  have habove : IsBoundedUnder (· ≤ ·) atTop (fun j => f j x) :=
    isBoundedUnder_of ⟨hi, fun j => (hb j).2⟩
  simp_rw [hperiod]
  exact liminf_add_const atTop (fun j => f j x) P habove.isCobounded_ge hbelow

end PoincareMT.M64
