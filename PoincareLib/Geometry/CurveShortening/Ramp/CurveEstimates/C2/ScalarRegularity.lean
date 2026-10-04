import PoincareLib.Geometry.CurveShortening.Ramp.CurveEstimates.C2.Continuity
import PoincareLib.Geometry.CurveShortening.Ramp.CurveEstimates.Relabeling.Regularity

/-!
# Spatial regularity and periodicity for the C2 solution record

The actual local theory supplies fixed C2 labels on positive subslabs.
Finite spatial regularity transports from M62, while closed continuity
extends squared-curvature periodicity to the original C2 endpoints.
Source: MT2007 Corollary 19.13, p. 446; correction pp. 6-9; see
`2026-09-21-c2-slope-preservation.md`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b T : ℝ} (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
  (hc : M63C2ShrinkingCurveOn F c (Icc a T))

include hc

/-- The actual C2 curve has periodic speed at every included time.
This uses its differentiable velocity and equal basepoints, MT2007 p. 446. -/
theorem c2_speed_periodic {t : ℝ} (ht : t ∈ Icc a T) :
    Function.Periodic (curveSpeed F c t) curvePeriod := by
  have hv := m63CurveVelocity_periodic
    ((hc.spatial_regular t ht).mdifferentiable (by norm_num)) (hc.periodic t ht)
  intro x
  have hvx : curveVelocity (fun y => c y t) (x + curvePeriod) =
      curveVelocity (fun y => c y t) x := hv x
  have hcx : c (x + curvePeriod) t = c x t := hc.periodic t ht x
  change (F.metric t).tangentNorm (c (x + curvePeriod) t)
      (curveVelocity (fun y => c y t) (x + curvePeriod)) =
    (F.metric t).tangentNorm (c x t) (curveVelocity (fun y => c y t) x)
  erw [hvx, hcx]

/-- The actual local theory gives precisely C1 speed and C2 curvature
scalars on each interior slice with the original C2 labels. These orders
suffice for the weighted comparison, MT2007 p. 446; correction pp. 6-9. -/
theorem c2_scalar_contDiff_of_local (hlocal : M63LocalCurveTheory F)
    {t : ℝ} (ht : t ∈ Ioo a T) :
    ContDiff ℝ 1 (curveSpeed F c t) ∧ ContDiff ℝ 2 (m62CurvatureSquared F c t) ∧
      ∀ epsilon : ℝ, 0 < epsilon →
        ContDiff ℝ 2 (m62RegularizedCurvature F c epsilon t) := by
  have hT : a < T := ht.1.trans ht.2
  have hTb : T ≤ b := (hc.domain_subset ⟨hT.le, le_rfl⟩).2
  obtain ⟨tau, hatau, htaut⟩ := exists_between ht.1
  obtain ⟨s, hts, hsT⟩ := exists_between ht.2
  have htaus := htaut.trans hts
  have hsub : Icc tau s ⊆ Icc a b := Icc_subset_Icc hatau.le (hsT.le.trans hTb)
  let Fs := m63RestrictClosedFlow F tau s hsub htaus
  obtain ⟨phi, d, hphi, _, hpos, _, hd, _, hcd⟩ :=
    hlocal.fixed_relabeling T hT hTb (Icc a T) (Or.inl rfl) c hc tau s
      hatau htaus hsT.le (Icc_subset_Icc hatau.le hsT.le)
  have hdM : M62ShrinkingCurve Fs d := m63SmoothRestriction hd tau s Subset.rfl htaus
  have ht' : t ∈ Icc tau s := ⟨htaut.le, hts.le⟩
  exact ⟨speed_contDiff_of_relabeling Fs hdM hphi hpos ht' (hcd t ht'),
    curvatureSquared_contDiff_of_relabeling Fs hdM hphi hpos ⟨htaut, hts⟩ (hcd t ht'),
    fun _ hepsilon => regularized_contDiff_of_relabeling Fs hdM hphi hpos
      ⟨htaut, hts⟩ (hcd t ht') hepsilon⟩

/-- Fixed labels give interior curvature periodicity, and direct C2
continuity extends it to both endpoints. Correction Lemma 0.4, pp. 7-8. -/
theorem c2_curvatureSquared_periodic (hlocal : M63LocalCurveTheory F)
    (hT : a < T) {t : ℝ} (ht : t ∈ Icc a T) :
    Function.Periodic (m62CurvatureSquared F c t) curvePeriod := by
  have hTb : T ≤ b := (hc.domain_subset ⟨hT.le, le_rfl⟩).2
  have hinterior (r : ℝ) (hr : r ∈ Ioo a T) :
      Function.Periodic (m62CurvatureSquared F c r) curvePeriod := by
    obtain ⟨tau, hatau, htaur⟩ := exists_between hr.1
    obtain ⟨s, hrs, hsT⟩ := exists_between hr.2
    have htaus := htaur.trans hrs
    have hsub : Icc tau s ⊆ Icc a b := Icc_subset_Icc hatau.le (hsT.le.trans hTb)
    let Fs := m63RestrictClosedFlow F tau s hsub htaus
    obtain ⟨phi, d, hphi, _, hpos, hshift, hd, _, hcd⟩ :=
      hlocal.fixed_relabeling T hT hTb (Icc a T) (Or.inl rfl) c hc tau s
        hatau htaus hsT.le (Icc_subset_Icc hatau.le hsT.le)
    have hdM : M62ShrinkingCurve Fs d := m63SmoothRestriction hd tau s Subset.rfl htaus
    have hr' : r ∈ Icc tau s := ⟨htaur.le, hrs.le⟩
    have heq (x : ℝ) := curvatureSquared_eq_of_relabeling Fs hdM
      (hphi.differentiable (by norm_num)) hpos hr' (hcd r hr') (x := x)
    intro x
    change m62CurvatureSquared Fs c r (x + curvePeriod) = m62CurvatureSquared Fs c r x
    rw [heq, heq, hshift, M62.curvatureSquared_periodic Fs d hdM ⟨htaur, hrs⟩]
  have hcont (x : ℝ) : ContinuousOn (fun s => m62CurvatureSquared F c s x) (Icc a T) :=
    (c2_curvatureSquared_continuousOn F c hc hT).comp
      (continuous_const.prodMk continuous_id).continuousOn (fun _ hs => ⟨mem_univ _, hs⟩)
  intro x
  have heq : EqOn (fun s => m62CurvatureSquared F c s (x + curvePeriod))
      (fun s => m62CurvatureSquared F c s x) (Ioo a T) :=
    fun s hs => hinterior s hs x
  exact heq.of_subset_closure (hcont (x + curvePeriod)) (hcont x)
    Ioo_subset_Icc_self (by rw [closure_Ioo hT.ne]) ht

/-- Regularization preserves closed-slab periodicity for every real epsilon.
Correction Lemma 0.4 and corrected Lemma 19.14, pp. 7-9. -/
theorem c2_regularized_periodic (hlocal : M63LocalCurveTheory F)
    (hT : a < T) (epsilon : ℝ) {t : ℝ} (ht : t ∈ Icc a T) :
    Function.Periodic (m62RegularizedCurvature F c epsilon t) curvePeriod := by
  intro x
  simp only [m62RegularizedCurvature, c2_curvatureSquared_periodic F c hc hlocal hT ht x]

end PoincareMT.M63
