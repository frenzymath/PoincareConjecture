import PoincareConjecture.Proofs.M59.Mathlib.ChartPatch
import PoincareConjecture.Proofs.M59.Mathlib.CompactMapControl
import PoincareConjecture.Proofs.M59.Mathlib.CoordinateApproximation











set_option autoImplicit false

open Set Filter Function
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M59

variable {E H X F K M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [T2Space X] [NormalSpace X] [SigmaCompactSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
  (J : ModelWithCorners ℝ F K) [J.Boundaryless]
  [MetricSpace M] [ChartedSpace K M] [IsManifold J ∞ M]




theorem exists_local_chart_approximation
    (c : M) (b : X → ℝ) (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b)
    (hbc : HasCompactSupport b) (hbI : ∀ x, b x ∈ Icc (0 : ℝ) 1)
    (f : X → M) (hf : Continuous f)
    (hsource : ∀ x ∈ tsupport b, f x ∈ (extChartAt J c).source)
    (p : M) {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ g : X → M, Continuous g ∧ (∀ x, dist (g x) (f x) < epsilon) ∧
      (∀ x, f x = p → g x = p) ∧
      (∀ x, ContMDiffAt I J ∞ f x → ContMDiffAt I J ∞ g x) ∧
      ∀ x, b =ᶠ[𝓝 x] 1 → ContMDiffAt I J ∞ g x := by
  let e := extChartAt J c
  let coords : X → F := fun x => e (f x)
  let U : Set X := f ⁻¹' e.source
  have hU : IsOpen U := (isOpen_extChartAt_source c).preimage hf
  have hcoords : ContinuousOn coords U := by
    intro x hx
    exact (((contMDiffAt_extChartAt' (by
        change f x ∈ (extChartAt J c).source at hx
        simpa only [extChartAt_source] using hx) :
      ContMDiffAt J 𝓘(ℝ, F) ∞ e (f x)).continuousAt).comp
        (f := f) hf.continuousAt).continuousWithinAt
  have hsub : tsupport b ⊆ U := hsource
  have hcompact : IsCompact (coords '' tsupport b) := hbc.image_of_continuousOn (hcoords.mono hsub)
  have htarget : coords '' tsupport b ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hsource x hx)
  have hinv : ∀ z ∈ coords '' tsupport b, ContinuousAt e.symm z := by
    intro z hz
    exact ((contMDiffOn_extChartAt_symm c).contMDiffAt
      ((isOpen_extChartAt_target c).mem_nhds (htarget hz)) :
        ContMDiffAt 𝓘(ℝ, F) J ∞ e.symm z).continuousAt
  obtain ⟨delta, hd, hcontrol⟩ := exists_uniform_compact_map_control e.symm hcompact
    (isOpen_extChartAt_target c) htarget hinv he
  obtain ⟨v, hv, hvclose, hvfix⟩ := exists_coordinate_approximation_preserving_value I
    hbc hU hsub coords hcoords (e p) hd
  have hcoordDist (x : X) (hx : x ∈ tsupport b) :
      dist ((1 - b x) • coords x + b x • v x) (coords x) < delta := by
    have heq : (1 - b x) • coords x + b x • v x - coords x = b x • (v x - coords x) := by
      simp only [sub_smul, one_smul, smul_sub]
      abel
    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hbI x).1]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hbI x).2).trans_lt
      (by simpa only [dist_eq_norm] using hvclose x hx)
  have hc (x : X) (hx : x ∈ tsupport b) :
      (1 - b x) • coords x + b x • v x ∈ e.target ∧
        dist (e.symm ((1 - b x) • coords x + b x • v x)) (f x) < epsilon := by
    have h := hcontrol (coords x) ⟨x, hx, rfl⟩ _ (hcoordDist x hx)
    simpa only [coords, e.left_inv (hsource x hx)] using h
  refine ⟨chartPatch J c b v f,
    continuous_chartPatch J c b v f hb.continuous hv.continuous hf hsource
      (fun x hx => (hc x hx).1), ?_, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : b x = 0
    · rw [chartPatch_of_weight_zero J c b v f hx, dist_self]
      exact he
    · simpa only [chartPatch, hx, if_false] using (hc x (subset_closure hx)).2
  · intro x hx
    exact chartPatch_preserves_value J c b v f hsource p
      (fun y hy hyp => hvfix y hy (congrArg e hyp)) hx
  · intro x hx
    exact contMDiffAt_chartPatch_of_contMDiffAt I J c b v f hb hv hsource
      (fun y hy => (hc y hy).1) hx
  · intro x hx
    exact contMDiffAt_chartPatch_of_plateau I J c b v f hv hf hsource
      (fun y hy => (hc y hy).1) hx

end PoincareConjecture.Proofs.M59
