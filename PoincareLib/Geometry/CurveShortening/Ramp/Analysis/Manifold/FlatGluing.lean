import PoincareLib.Geometry.CurveShortening.Ramp.Analysis.Flat.JetGluing
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Manifold gluing after a flat scalar parameter

A common actual target chart reduces gluing of two smooth curve germs to
matching their scalar-parameter jets. The branch test is at the source
join, so the inner parameter need not be monotone. This is the local
vertex argument for MT2007 pp. 451-452; see
`2026-09-21-manifold-flat-gluing.md`.
-/

set_option autoImplicit false

open Filter Set
open scoped ContDiff Manifold Topology

/-- Smooth manifold germs with the same value glue after a smooth flat
inner parameter. No separation or completeness hypothesis is needed.
The source-half-line join is the one used in MT2007 pp. 451-452. -/
theorem contMDiffAt_piecewise_comp_of_flat
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {f g : ℝ → M} {phi : ℝ → ℝ} {c x : ℝ}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ f c)
    (hg : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ g c) (hfg : f c = g c)
    (hphi : ContDiffAt ℝ ∞ phi x) (hphi_eq : phi x = c)
    (hflat : ∀ i : ℕ, 0 < i → iteratedDeriv i phi x = 0) :
    ContMDiffAt 𝓘(ℝ, ℝ) I ∞ ((Iic x).piecewise (f ∘ phi) (g ∘ phi)) x := by
  let h : ℝ → M := (Iic x).piecewise (f ∘ phi) (g ∘ phi)
  let e := extChartAt I (f c)
  have hf0 : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ f (phi x) := by
    simpa only [hphi_eq] using hf
  have hg0 : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ g (phi x) := by
    simpa only [hphi_eq] using hg
  have hvalue : h x = f c := by simp [h, hphi_eq]
  have hcont : ContinuousAt h x := by
    change Tendsto h (𝓝 x) (𝓝 (h x))
    rw [hvalue]
    have hft : Tendsto (f ∘ phi) (𝓝 x) (𝓝 (f c)) := by
      simpa only [ContinuousAt, Function.comp_apply, hphi_eq] using
        hf0.continuousAt.comp hphi.continuousAt
    have hgt : Tendsto (g ∘ phi) (𝓝 x) (𝓝 (f c)) := by
      simpa only [ContinuousAt, Function.comp_apply, hphi_eq, hfg] using
        hg0.continuousAt.comp hphi.continuousAt
    exact hft.if' hgt
  have hgc : g c ∈ (chartAt H (f c)).source := by
    rw [← hfg]
    exact mem_chart_source H (f c)
  have hfe : ContDiffAt ℝ ∞ (e ∘ f) c :=
    ((contMDiffAt_iff_target_of_mem_source (mem_chart_source H (f c))).mp hf).2.contDiffAt
  have hge : ContDiffAt ℝ ∞ (e ∘ g) c :=
    ((contMDiffAt_iff_target_of_mem_source hgc).mp hg).2.contDiffAt
  have hfe0 : ContDiffAt ℝ ∞ (e ∘ f) (phi x) := by simpa only [hphi_eq] using hfe
  have hge0 : ContDiffAt ℝ ∞ (e ∘ g) (phi x) := by simpa only [hphi_eq] using hge
  have hjets (i : ℕ) :
      iteratedDeriv i ((e ∘ f) ∘ phi) x = iteratedDeriv i ((e ∘ g) ∘ phi) x := by
    by_cases hi : i = 0
    · subst i
      simp only [iteratedDeriv_zero, Function.comp_apply, hphi_eq, hfg]
    · rw [iteratedDeriv_scomp_eq_zero_of_flat hfe0 hphi hflat (Nat.pos_of_ne_zero hi),
        iteratedDeriv_scomp_eq_zero_of_flat hge0 hphi hflat (Nat.pos_of_ne_zero hi)]
  have heq : e ∘ h = (Iic x).piecewise ((e ∘ f) ∘ phi) ((e ∘ g) ∘ phi) := by
    funext y
    by_cases hy : y ≤ x <;> simp [h, hy, Function.comp_def]
  have hcoord : ContDiffAt ℝ ∞ (e ∘ h) x := by
    rw [heq]
    exact contDiffAt_infty_piecewise_Iic_of_iteratedDeriv_eq
      (hfe0.comp x hphi) (hge0.comp x hphi) hjets
  have hsource : h x ∈ (chartAt H (f c)).source := by
    rw [hvalue]
    exact mem_chart_source H (f c)
  exact (contMDiffAt_iff_target_of_mem_source hsource).mpr ⟨hcont, hcoord.contMDiffAt⟩
