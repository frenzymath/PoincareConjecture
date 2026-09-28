import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.PicardLindelof

noncomputable section
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
namespace Poincare.ODE.Parameter

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem eq_const_of_hasDerivWithinAt_of_eq_zero
    {f : F → F} {z₀ : F} {s : Set F} {K : ℝ≥0}
    (hlip : LipschitzOnWith K f s) (heq : f z₀ = 0)
    {ε : ℝ} (hε : 0 < ε) {α : ℝ → F} (hα0 : α 0 = z₀)
    (hd : ∀ t ∈ Icc (-ε) ε, HasDerivWithinAt α (f (α t)) (Icc (-ε) ε) t)
    (hmem : ∀ t ∈ Icc (-ε) ε, α t ∈ s) (hz₀s : z₀ ∈ s)
    {t : ℝ} (ht : t ∈ Icc (-ε) ε) : α t = z₀ := by
  have h0mem : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.mpr hε, hε⟩
  have hcont : ContinuousOn α (Icc (-ε) ε) :=
    fun u hu => (hd u hu).continuousWithinAt
  have heqOn : EqOn α (fun _ => z₀) (Icc (-ε) ε) := by
    refine ODE_solution_unique_of_mem_Icc (v := fun _ => f) (s := fun _ => s)
      (fun u _ => hlip) h0mem hcont ?_ (fun u hu => hmem u (Ioo_subset_Icc_self hu))
      continuousOn_const ?_ (fun _ _ => hz₀s) (by simpa using hα0)
    · intro u hu
      exact (hd u (Ioo_subset_Icc_self hu)).hasDerivAt
        (Icc_mem_nhds hu.1 hu.2)
    · intro u hu
      simpa [heq] using (hasDerivAt_const u z₀)
  exact heqOn ht

variable [CompleteSpace F]

theorem exists_forall_hasDerivWithinAt_lipschitzOnWith_of_contDiffAt
    {f : F → F} {z₀ : F} (hf : ContDiffAt ℝ 1 f z₀)
    {U : Set F} (hU : U ∈ 𝓝 z₀) :
    ∃ (r ε : ℝ) (Z : F → ℝ → F) (L : ℝ≥0), 0 < r ∧ 0 < ε ∧
      (∀ z ∈ closedBall z₀ r,
        Z z 0 = z ∧
        (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z) (f (Z z t)) (Icc (-ε) ε) t) ∧
        (∀ t ∈ Icc (-ε) ε, Z z t ∈ U)) ∧
      (∀ t ∈ Icc (-ε) ε, LipschitzOnWith L (Z · t) (closedBall z₀ r)) := by
  classical
  obtain ⟨ε₁, hε₁, a, r₁, L₀, K, hr₁, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hf
  have hpl0 := hpl 0
  obtain ⟨Z, hZ, L, hLip⟩ :=
    hpl0.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp hU
  have hZ₀ := hZ z₀ (mem_closedBall_self hr₁.le)
  have hIcc0 : (0 : ℝ) ∈ Icc (0 - ε₁) (0 + ε₁) := by
    constructor <;> [linarith; linarith]
  have hcont0 : ContinuousWithinAt (Z z₀) (Icc (0 - ε₁) (0 + ε₁)) 0 := by
    have := (hZ₀.2 0 hIcc0).continuousWithinAt
    exact this
  have hcenter0 : Z z₀ 0 = z₀ := hZ₀.1
  have hhalf : (0 : ℝ) < δ / 2 := by positivity
  have hev : ∀ᶠ t in 𝓝[Icc (0 - ε₁) (0 + ε₁)] (0 : ℝ),
      Z z₀ t ∈ ball z₀ (δ / 2) := by
    have : ball z₀ (δ / 2) ∈ 𝓝 (Z z₀ 0) := by
      rw [hcenter0]
      exact ball_mem_nhds z₀ hhalf
    exact hcont0.eventually_mem this
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhdsWithin_iff.mp hev
  set r : ℝ := min r₁ (δ / (2 * (L + 1))) with hrdef
  set ε : ℝ := min (min ε₁ (η / 2)) 1 with hεdef
  have hrpos : 0 < r := lt_min hr₁ (by positivity)
  have hεpos : 0 < ε := lt_min (lt_min hε₁ (by positivity)) one_pos
  have hεε₁ : ε ≤ ε₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hIccsub : Icc (-ε) ε ⊆ Icc (0 - ε₁) (0 + ε₁) := by
    apply Icc_subset_Icc <;> [linarith; linarith]
  have hrr₁ : r ≤ r₁ := min_le_left _ _
  have hballsub : closedBall z₀ r ⊆ closedBall z₀ r₁ :=
    closedBall_subset_closedBall hrr₁
  refine ⟨r, ε, Z, L, hrpos, hεpos, ?_, ?_⟩
  · intro z hz
    have hz₁ : z ∈ closedBall z₀ r₁ := hballsub hz
    obtain ⟨hz0, hzd⟩ := hZ z hz₁
    refine ⟨hz0, fun t ht => (hzd t (hIccsub ht)).mono hIccsub, ?_⟩
    intro t ht
    have htmem : t ∈ Icc (0 - ε₁) (0 + ε₁) := hIccsub ht
    have hLipt := hLip t htmem
    have hd1 : dist (Z z t) (Z z₀ t) ≤ L * dist z z₀ := by
      have := hLipt.dist_le_mul z hz₁ z₀ (mem_closedBall_self hr₁.le)
      simpa using this
    have hd1' : dist (Z z t) (Z z₀ t) ≤ L * r := by
      refine hd1.trans ?_
      have : dist z z₀ ≤ r := mem_closedBall.mp hz
      exact mul_le_mul_of_nonneg_left this L.coe_nonneg
    have htη : t ∈ ball (0 : ℝ) η := by
      rw [mem_ball, Real.dist_eq, sub_zero]
      have h1 : |t| ≤ ε := abs_le.mpr ⟨ht.1, ht.2⟩
      have h2 : ε ≤ η / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
      linarith
    have hd2 : Z z₀ t ∈ ball z₀ (δ / 2) := hηsub ⟨htη, htmem⟩
    have hLr : (L : ℝ) * r ≤ δ / 2 := by
      have hrle : r ≤ δ / (2 * ((L : ℝ) + 1)) := min_le_right _ _
      have hpos : (0 : ℝ) < 2 * ((L : ℝ) + 1) := by positivity
      have h1 : (L : ℝ) * r ≤ (L : ℝ) * (δ / (2 * ((L : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hrle L.coe_nonneg
      have h2 : (L : ℝ) * (δ / (2 * ((L : ℝ) + 1))) ≤ δ / 2 := by
        have hc0 : (0 : ℝ) ≤ δ / (2 * ((L : ℝ) + 1)) := by positivity
        have hcδ : δ / (2 * ((L : ℝ) + 1)) * (2 * ((L : ℝ) + 1)) = δ :=
          div_mul_cancel₀ δ (ne_of_gt hpos)
        nlinarith [L.coe_nonneg, hc0, hcδ]
      linarith
    apply hδU
    have : dist (Z z t) z₀ ≤ dist (Z z t) (Z z₀ t) + dist (Z z₀ t) z₀ :=
      dist_triangle _ _ _
    have hlt : dist (Z z t) z₀ < δ := by
      have h2 := mem_ball.mp hd2
      calc dist (Z z t) z₀ ≤ dist (Z z t) (Z z₀ t) + dist (Z z₀ t) z₀ := this
        _ ≤ L * r + dist (Z z₀ t) z₀ := by linarith
        _ < δ / 2 + δ / 2 := by linarith
        _ = δ := by ring
    exact mem_ball.mpr hlt
  · intro t ht
    exact (hLip t (hIccsub ht)).mono hballsub

end Poincare.ODE.Parameter
