import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.UniformSpace.HeineCantor










set_option autoImplicit false

open Set Metric

namespace Poincare.Manifold.Schoenflies.Plane

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f f' : ℝ → E} {a b ε : ℝ} {v : E}



theorem norm_slope_sub_le_of_deriv_sub_le (hab : a < b)
    (hd : ∀ s ∈ Icc a b, HasDerivWithinAt f (f' s) (Icc a b) s)
    (hb : ∀ s ∈ Icc a b, ‖f' s - v‖ ≤ ε) : ‖slope f a b - v‖ ≤ ε := by
  let g : ℝ → E := fun s => f s - s • v
  have hg : ∀ s ∈ Icc a b, HasDerivWithinAt g (f' s - v) (Icc a b) s := by
    intro s hs
    simpa only [g, id_eq, one_smul] using (hd s hs).fun_sub
      ((hasDerivWithinAt_id (x := s) (s := Icc a b)).smul_const v)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hg hb
    (convex_Icc a b) (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le)
  have heq : g b - g a = f b - f a - (b - a) • v := by
    dsimp [g]
    simp only [sub_smul]
    abel
  rw [heq, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hab)] at h
  have hne : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have hs : slope f a b - v = (b - a)⁻¹ • (f b - f a - (b - a) • v) := by
    simp only [slope_def_module, smul_sub, smul_smul, inv_mul_cancel₀ hne, one_smul]
  calc
    ‖slope f a b - v‖ = (b - a)⁻¹ * ‖f b - f a - (b - a) • v‖ := by
      rw [hs, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (sub_pos.mpr hab))]
    _ ≤ (b - a)⁻¹ * (ε * (b - a)) :=
      mul_le_mul_of_nonneg_left h (le_of_lt (inv_pos.mpr (sub_pos.mpr hab)))
    _ = ε := by rw [mul_left_comm, inv_mul_cancel₀ hne, mul_one]



theorem norm_chord_sub_le_of_deriv_sub_le (hab : a ≤ b)
    (hd : ∀ s ∈ Icc a b, HasDerivWithinAt f (f' s) (Icc a b) s)
    (hb : ∀ s ∈ Icc a b, ‖f' s - v‖ ≤ ε)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    ‖AffineMap.lineMap (f a) (f b) t - f (AffineMap.lineMap a b t)‖ ≤ 2 * ε * (b - a) := by
  let g : ℝ → E := fun s => f s - s • v
  have hg : ∀ s ∈ Icc a b, HasDerivWithinAt g (f' s - v) (Icc a b) s := by
    intro s hs
    simpa only [g, id_eq, one_smul] using (hd s hs).fun_sub
      ((hasDerivWithinAt_id (x := s) (s := Icc a b)).smul_const v)
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hb a (left_mem_Icc.mpr hab))
  let s := AffineMap.lineMap a b t
  have hs : s ∈ Icc a b := by
    dsimp [s]
    rw [AffineMap.lineMap_apply_ring']
    constructor <;> nlinarith [ht.1, ht.2]
  have hm (x : ℝ) (hx : x ∈ Icc a b) : ‖g x - g a‖ ≤ ε * (x - a) := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hg hb
      (convex_Icc a b) (left_mem_Icc.mpr hab) hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hx.1)] using h
  have heq : AffineMap.lineMap (f a) (f b) t - f s =
      t • (g b - g a) - (g s - g a) := by
    dsimp [g, s]
    rw [AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_ring']
    simp only [smul_sub, sub_smul, add_smul, mul_smul]
    abel
  change ‖AffineMap.lineMap (f a) (f b) t - f s‖ ≤ _
  rw [heq]
  calc
    ‖t • (g b - g a) - (g s - g a)‖ ≤ ‖t • (g b - g a)‖ + ‖g s - g a‖ := norm_sub_le _ _
    _ = t * ‖g b - g a‖ + ‖g s - g a‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    _ ≤ t * (ε * (b - a)) + ε * (s - a) :=
      add_le_add (mul_le_mul_of_nonneg_left (hm b (right_mem_Icc.mpr hab)) ht.1) (hm s hs)
    _ ≤ ε * (b - a) + ε * (b - a) := add_le_add
      (mul_le_of_le_one_left (mul_nonneg hε (sub_nonneg.mpr hab)) ht.2)
      (mul_le_mul_of_nonneg_left (sub_le_sub_right hs.2 a) hε)
    _ = 2 * ε * (b - a) := by ring



theorem exists_uniform_chord_estimates {X : Type*} [PseudoMetricSpace X]
    {K : Set X} (hK : IsCompact K) {c d : X → ℝ → E} {l u : ℝ}
    (hd : ∀ z ∈ K, ∀ s ∈ Icc l u, HasDerivWithinAt (c z) (d z s) (Icc l u) s)
    (hcont : ContinuousOn (fun p : X × ℝ => d p.1 p.2) (K ×ˢ Icc l u))
    {ε : ℝ} (he : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, ∀ a ∈ Icc l u, ∀ b ∈ Icc l u,
      a < b → b - a < δ →
      ‖slope (c z) a b - d z a‖ ≤ ε ∧
        ∀ t ∈ Icc (0 : ℝ) 1,
          ‖AffineMap.lineMap (c z a) (c z b) t - c z (AffineMap.lineMap a b t)‖ ≤
            2 * ε * (b - a) := by
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    ((hK.prod isCompact_Icc).uniformContinuousOn_of_continuous hcont) ε he
  refine ⟨δ, hδ, ?_⟩
  intro z hz a ha b hb hab hmesh
  have hsub : Icc a b ⊆ Icc l u := fun s hs => ⟨ha.1.trans hs.1, hs.2.trans hb.2⟩
  have hder : ∀ s ∈ Icc a b, HasDerivWithinAt (c z) (d z s) (Icc a b) s :=
    fun s hs => (hd z hz s (hsub hs)).mono hsub
  have hbound : ∀ s ∈ Icc a b, ‖d z s - d z a‖ ≤ ε := by
    intro s hs
    have hdist : dist (z, s) (z, a) < δ := by
      rw [dist_prod_same_left, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs.1)]
      exact (sub_le_sub_right hs.2 a).trans_lt hmesh
    have h := hclose (z, s) ⟨hz, hsub hs⟩ (z, a) ⟨hz, ha⟩ hdist
    exact le_of_lt (by simpa only [dist_eq_norm] using h)
  exact ⟨norm_slope_sub_le_of_deriv_sub_le hab hder hbound,
    fun t ht => norm_chord_sub_le_of_deriv_sub_le hab.le hder hbound ht⟩

end Poincare.Manifold.Schoenflies.Plane
