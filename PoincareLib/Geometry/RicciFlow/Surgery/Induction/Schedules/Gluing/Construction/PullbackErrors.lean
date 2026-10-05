import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.Gluing.Estimates.VanishingJets

/-!
# Algebra of vanishing coordinate errors

The fixed-coordinate gluing identity uses sums, bounded scalar factors,
and actual bilinear pullbacks. Their finite jets vanish by the ordinary
Taylor and Leibniz estimates. Source: Proposition 15.2, pp. 353-354;
see GluingCompactness.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter
open scoped ContDiff Topology

namespace PoincareMT.M45

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace PointJetsVanish

variable {l : Filter ι} {x : ι → E} {f g : ι → E → F}

/-- Equality on each actual neighborhood preserves vanishing jets.
Derivation: GluingCompactness.md, applying Proposition 15.2, pp. 353-354. -/
theorem congr (hf : PointJetsVanish f x l)
    (heq : ∀ i, f i =ᶠ[𝓝 (x i)] g i) : PointJetsVanish g x l := by
  intro m
  have h : (fun i => iteratedFDeriv ℝ m (f i) (x i)) =
      fun i => iteratedFDeriv ℝ m (g i) (x i) := by
    funext i
    exact ((heq i).iteratedFDeriv (𝕜 := ℝ) m).self_of_nhds
  rw [← h]
  exact hf m

/-- Adding two smooth errors whose finite jets vanish preserves this property.
Derivation: GluingCompactness.md, applying Proposition 15.2, pp. 353-354. -/
theorem add (hf : PointJetsVanish f x l) (hg : PointJetsVanish g x l)
    (hfs : ∀ i, ContDiffAt ℝ ∞ (f i) (x i))
    (hgs : ∀ i, ContDiffAt ℝ ∞ (g i) (x i)) :
    PointJetsVanish (fun i y => f i y + g i y) x l := by
  intro m
  simpa only [fun_iteratedFDeriv_add_apply
    ((hfs _).of_le (by exact_mod_cast le_top))
    ((hgs _).of_le (by exact_mod_cast le_top)), add_zero]
    using (hf m).add (hg m)

/-- Subtracting two smooth errors whose finite jets vanish preserves this property.
Derivation: GluingCompactness.md, applying Proposition 15.2, pp. 353-354. -/
theorem sub (hf : PointJetsVanish f x l) (hg : PointJetsVanish g x l)
    (hfs : ∀ i, ContDiffAt ℝ ∞ (f i) (x i))
    (hgs : ∀ i, ContDiffAt ℝ ∞ (g i) (x i)) :
    PointJetsVanish (fun i y => f i y - g i y) x l := by
  intro m
  simpa only [fun_iteratedFDeriv_sub_apply
    ((hfs _).of_le (by exact_mod_cast le_top))
    ((hgs _).of_le (by exact_mod_cast le_top)), sub_self]
    using (hf m).sub (hg m)

/-- A scalar factor bounded along the sequence preserves vanishing spatial jets.
Derivation: GluingCompactness.md, applying Proposition 15.2, pp. 353-354. -/
theorem smul (hf : PointJetsVanish f x l) {c : ι → ℝ}
    (hc : l.IsBoundedUnder (· ≤ ·) (fun i => ‖c i‖))
    (hfs : ∀ i, ContDiffAt ℝ ∞ (f i) (x i)) :
    PointJetsVanish (fun i y => c i • f i y) x l := by
  intro m
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hz : Tendsto (fun i => ‖iteratedFDeriv ℝ m (f i) (x i)‖) l (𝓝 0) := by
    simpa only [norm_zero] using (hf m).norm
  have hb : l.IsBoundedUnder (· ≤ ·) (fun i => ‖‖c i‖‖) := by
    simpa only [norm_norm] using hc
  simpa only [iteratedFDeriv_const_smul_apply'
    ((hfs _).of_le (by exact_mod_cast le_top)),
    norm_smul, Real.norm_eq_abs, abs_abs, mul_comm] using hz.zero_mul_isBoundedUnder_le hb

end PointJetsVanish

/-- Two smooth families with identical limiting jets have vanishing difference jets.
Derivation: GluingCompactness.md, applying Proposition 15.2, pp. 353-354. -/
theorem PointJetsConverge.sub_vanish {l : Filter ι} {x : ι → E}
    {f g : ι → E → F} {f0 : E → F} {x0 : E}
    (hf : PointJetsConverge f x f0 x0 l) (hg : PointJetsConverge g x f0 x0 l)
    (hfs : ∀ i, ContDiffAt ℝ ∞ (f i) (x i))
    (hgs : ∀ i, ContDiffAt ℝ ∞ (g i) (x i)) :
    PointJetsVanish (fun i y => f i y - g i y) x l := by
  intro m
  simpa only [fun_iteratedFDeriv_sub_apply
    ((hfs _).of_le (by exact_mod_cast le_top))
    ((hgs _).of_le (by exact_mod_cast le_top)), sub_self]
    using (hf m).sub (hg m)

end PoincareMT.M45
