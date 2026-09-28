import PoincareConjecture.Proofs.M63.Mathlib.CompactParameterNeighborhood
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicSmoothApproximation
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessEmbeddedCurve

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι

theorem exists_c2ShrinkingCurve_embedded_C1_neighborhood
    {F : RicciFlow n M (Icc a b)} {c : ℝ → ℝ → M} {J : Set ℝ}
    (hc : M63C2ShrinkingCurveOn F c J) {e : M → W}
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {r : ℝ → W} (hr : ContDiff ℝ 1 r) (hrper : Function.Periodic r curvePeriod)
    {s T : ℝ} (hsT : s < T) (hJ : Icc s T ⊆ J)
    {eps eta : ℝ} (_heps : 0 < eps) (_heta : 0 < eta)
    (hclose : ∀ x, ‖e (c x s) - r x‖ < eps)
    (hfirst : ∀ x, ‖deriv (fun y => e (c y s)) x - deriv r x‖ < eta) :
    ∃ tau : ℝ, s < tau ∧ tau ≤ T ∧ ∀ t ∈ Icc s tau, ∀ x,
      ‖e (c x t) - r x‖ < eps ∧
      ‖deriv (fun y => e (c y t)) x - deriv r x‖ < eta := by
  obtain ⟨hqC2, _, hq, hq₁, _⟩ := c2ShrinkingCurve_embedded_closed_data hc he
  let K := Icc (0 : ℝ) curvePeriod
  let : CompactSpace K := isCompact_iff_compactSpace.mp isCompact_Icc
  let S := Icc s T
  let s₀ : S := ⟨s, le_rfl, hsT.le⟩
  let f : S × K → W × W := fun p =>
    (e (c p.2.1 p.1.1) - r p.2.1,
      deriv (fun y => e (c y p.1.1)) p.2.1 - deriv r p.2.1)
  have hswap : Continuous (fun p : S × K => (p.2.1, p.1.1)) :=
    (continuous_subtype_val.comp continuous_snd).prodMk
      (continuous_subtype_val.comp continuous_fst)
  have hmap (p : S × K) : (p.2.1, p.1.1) ∈ univ ×ˢ J :=
    ⟨mem_univ _, hJ p.1.2⟩
  have hf : Continuous f :=
    ((hq.comp_continuous hswap hmap).sub
      (hr.continuous.comp (continuous_subtype_val.comp continuous_snd))).prodMk
      ((hq₁.comp_continuous hswap hmap).sub
        (hr.continuous_deriv_one.comp (continuous_subtype_val.comp continuous_snd)))
  have hinitial (x : K) : f (s₀, x) ∈ Metric.ball (0 : W) eps ×ˢ Metric.ball (0 : W) eta := by
    simpa only [f, s₀, mem_prod, Metric.mem_ball, dist_zero_right] using
      And.intro (hclose x.1) (hfirst x.1)
  obtain ⟨δ, hδ, hnear⟩ := exists_uniform_open_parameter_radius hf
    (Metric.isOpen_ball.prod Metric.isOpen_ball) hinitial
  let tau := min T (s + δ / 2)
  have hstau : s < tau := lt_min hsT (by linarith)
  have htauT : tau ≤ T := min_le_left _ _
  have hper (t : ℝ) (ht : t ∈ Icc s T) :
      Function.Periodic (fun x =>
        (e (c x t) - r x, deriv (fun y => e (c y t)) x - deriv r x)) curvePeriod := by
    have hp : Function.Periodic (fun x => e (c x t)) curvePeriod :=
      fun x => congrArg e (hc.periodic t (hJ ht) x)
    have hp₁ := hp.deriv_of_differentiable
      ((hqC2 t (hJ ht)).differentiable (by norm_num))
    have hr₁ := hrper.deriv_of_differentiable (hr.differentiable (by norm_num))
    intro x
    exact Prod.ext (congrArg₂ (fun u v : W => u - v) (hp x) (hrper x))
      (congrArg₂ (fun u v : W => u - v) (hp₁ x) (hr₁ x))
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  refine ⟨tau, hstau, htauT, fun t ht x => ?_⟩
  have htS : t ∈ S := ⟨ht.1, ht.2.trans htauT⟩
  have htδ : dist (⟨t, htS⟩ : S) s₀ < δ := by
    have hupper : t ≤ s + δ / 2 := ht.2.trans (min_le_right _ _)
    change dist t s < δ
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith
  obtain ⟨y, hy, heq⟩ := (hper t htS).exists_mem_Ico₀ hP x
  have hyK : y ∈ K := ⟨hy.1, hy.2.le⟩
  have hybound := hnear ⟨t, htS⟩ htδ ⟨y, hyK⟩
  change (e (c y t) - r y, deriv (fun z => e (c z t)) y - deriv r y) ∈
    Metric.ball (0 : W) eps ×ˢ Metric.ball (0 : W) eta at hybound
  rw [← heq] at hybound
  simpa only [mem_prod, Metric.mem_ball, dist_zero_right] using hybound

end PoincareConjecture.M63
