import PoincareConjecture.Proofs.M09.PicardNeighborhood
import PoincareConjecture.Proofs.M09.PathRescale

set_option autoImplicit false

open scoped ContDiff Topology
open Set Filter Metric

namespace PoincareConjecture.Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_local_smooth_flow (f : C(E, E)) (hf : ContDiff ℝ ∞ f) (x0 : E) :
    ∃ (alpha : E × ℝ → E) (V : Set E) (d : ℝ),
      IsOpen V ∧ x0 ∈ V ∧ 0 < d ∧
      ContDiffOn ℝ ∞ alpha (V ×ˢ Set.Ioo (-d) d) ∧
      (∀ x ∈ V, alpha (x, 0) = x) ∧
      ∀ x ∈ V, ∀ a ∈ Set.Ioo (-d) d,
        HasDerivAt (fun t ↦ alpha (x, t)) (f (alpha (x, a))) a := by
  obtain ⟨sigma, U, W, hU, hxU, hW, hxW, hsigma, hsmooth, heq, huniq⟩ :=
    exists_scaledPicard_neighborhood f hf x0
  let endpoint : Set.Icc (-1 : ℝ) 1 := ⟨1, by norm_num⟩
  let alpha : E × ℝ → E := fun p ↦ sigma p endpoint
  have haSmooth : ContDiffOn ℝ ∞ alpha U :=
    (ContinuousMap.evalCLM (R := ℝ) (M := E) endpoint).contDiff.comp_contDiffOn hsmooth
  obtain ⟨e, he, heW⟩ := Metric.isOpen_iff.mp hW _ hxW
  have hcont : ContinuousAt sigma (x0, (0 : ℝ)) :=
    (hsmooth.contDiffAt (hU.mem_nhds hxU)).continuousAt
  have hclose : ∀ᶠ p in 𝓝 (x0, (0 : ℝ)),
      dist (sigma p) (ContinuousMap.const _ x0) < e := by
    simpa only [hsigma, Metric.mem_ball] using
      hcont.tendsto.eventually (Metric.ball_mem_nhds (sigma (x0, 0)) he)
  obtain ⟨b, hb, hbsub⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (hU.mem_nhds hxU) hclose)
  let r := min b e
  have hr : 0 < r := lt_min hb he
  have hrb : r ≤ b := min_le_left _ _
  have hre : r ≤ e := min_le_right _ _
  have hparam {x : E} {a : ℝ} (hx : dist x x0 < r / 2) (ha : |a| ≤ r / 2) :
      (x, a) ∈ U ∧ dist (sigma (x, a)) (ContinuousMap.const _ x0) < e := by
    apply hbsub
    change dist (x, a) (x0, (0 : ℝ)) < b
    rw [Prod.dist_eq, Real.dist_eq, sub_zero]
    exact max_lt (by linarith) (by linarith)
  have hrect : ball x0 (r / 2) ×ˢ Set.Ioo (-(r / 4)) (r / 4) ⊆ U := by
    intro z hz
    exact (hparam hz.1 (by have h := abs_lt.mpr hz.2; linarith)).1
  refine ⟨alpha, ball x0 (r / 2), r / 4, isOpen_ball,
    mem_ball_self (by positivity), by positivity, haSmooth.mono hrect, ?_, ?_⟩
  · intro x hx
    have hx0 := hparam hx (a := 0) (by simp only [abs_zero]; positivity)
    have h := congrArg (fun v : C(Set.Icc (-1 : ℝ) 1, E) ↦ v endpoint)
      (heq (x, 0) hx0.1).2
    simpa only [zero_smul, add_zero, ContinuousMap.const_apply] using h
  · intro x hx a ha
    let a0 := r / 2
    have ha0 : 0 < a0 := by dsimp [a0]; positivity
    have ha0abs : |a0| ≤ r / 2 := by rw [abs_of_pos ha0]
    have hx0 := hparam hx ha0abs
    let v0 := sigma (x, a0)
    have hv0 : v0 = ContinuousMap.const _ x + a0 • pathPrimitive (f.comp v0) :=
      (heq (x, a0) hx0.1).2
    have hscale {t : ℝ} (ht : t ∈ Set.Ioo (-(r / 4)) (r / 4)) : |t / a0| < 1 := by
      rw [abs_div, abs_of_pos ha0]
      apply (div_lt_one ha0).mpr
      have ht' := abs_lt.mpr ht
      dsimp [a0]
      linarith
    have hrep : ∀ t ∈ Set.Ioo (-(r / 4)) (r / 4),
        alpha (x, t) = v0 (symmetricTimeProjection (t / a0)) := by
      intro t ht
      have htc := hscale ht
      have hw : ((x, t), pathRescale (t / a0) v0) ∈ W := by
        apply heW
        change dist ((x, t), pathRescale (t / a0) v0)
          ((x0, (0 : ℝ)), ContinuousMap.const _ x0) < e
        rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, sub_zero]
        refine max_lt (max_lt ?_ ?_) ?_
        · change dist x x0 < e
          have hxd : dist x x0 < r / 2 := hx
          linarith
        · have ht' := abs_lt.mpr ht
          linarith
        · rw [dist_eq_norm]
          exact (pathRescale_norm_sub_const_le (t / a0) v0 x0).trans_lt
            (by simpa only [dist_eq_norm] using hx0.2)
      have hmul : a0 * (t / a0) = t := by field_simp [ha0.ne']
      have hpath : pathRescale (t / a0) v0 = ContinuousMap.const _ x +
          t • pathPrimitive (f.comp (pathRescale (t / a0) v0)) := by
        simpa only [hmul] using pathRescale_picard f x a0 (t / a0) v0 hv0 htc.le
      have h := congrArg (fun v : C(Set.Icc (-1 : ℝ) 1, E) ↦ v endpoint)
        ((huniq ((x, t), pathRescale (t / a0) v0) hw).mp hpath)
      simpa only [pathRescale_apply, endpoint, mul_one] using h
    have hd := (picard_path_hasDerivAt f x a0 v0 hv0 (a / a0)
      (abs_lt.mp (hscale ha))).scomp a ((hasDerivAt_id a).div_const a0)
    have hd' : HasDerivAt (fun t ↦ v0 (symmetricTimeProjection (t / a0)))
        (f (alpha (x, a))) a := by
      simpa only [Function.comp_def, id_eq, one_div, smul_smul, inv_mul_cancel₀ ha0.ne',
        one_smul, ← hrep a ha] using hd
    apply hd'.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ha.1 ha.2] with t ht
    exact hrep t ht

end PoincareConjecture.Proofs.M09
