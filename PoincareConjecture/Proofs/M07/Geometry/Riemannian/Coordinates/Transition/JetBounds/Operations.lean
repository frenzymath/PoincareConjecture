import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Transition.JetBounds

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.CoordinateTransition

variable {ι E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

private theorem bound_all_orders {n : ℕ} {s : Set E} {f : ι → E → F}
    (h : HasUniformJetBoundsOn n s f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m, m ≤ n → ∀ i x, x ∈ s →
      ‖iteratedFDeriv ℝ m (f i) x‖ ≤ C := by
  classical
  choose c hc using fun j : Finset.range (n + 1) =>
    h.bound_nonneg (Nat.le_of_lt_succ (Finset.mem_range.1 j.2))
  refine ⟨∑ j, c j, Finset.sum_nonneg (fun j _ => (hc j).1), ?_⟩
  intro m hm i x hx
  let j : Finset.range (n + 1) := ⟨m, Finset.mem_range.mpr (Nat.lt_succ_of_le hm)⟩
  exact ((hc j).2 i x hx).trans
    (Finset.single_le_sum (fun k _ => (hc k).1) (Finset.mem_univ j))

theorem HasUniformJetBoundsOn.congr {n : ℕ} {s : Set E} (hs : IsOpen s)
    {f g : ι → E → F} (h : HasUniformJetBoundsOn n s f)
    (heq : ∀ i, EqOn (f i) (g i) s) : HasUniformJetBoundsOn n s g :=
  (HasUniformJetBoundsOn.congr_of_eventuallyEq hs heq).mp h

theorem HasUniformJetBoundsOn.sub {n : ℕ} {s : Set E} (hs : IsOpen s)
    {f g : ι → E → F} (hf : HasUniformJetBoundsOn n s f)
    (hg : HasUniformJetBoundsOn n s g)
    (hcf : ∀ i, ContDiffOn ℝ ∞ (f i) s) (hcg : ∀ i, ContDiffOn ℝ ∞ (g i) s) :
    HasUniformJetBoundsOn n s (fun i x => f i x - g i x) := by
  intro m hm
  obtain ⟨Cf, hCf⟩ := hf m hm
  obtain ⟨Cg, hCg⟩ := hg m hm
  refine ⟨Cf + Cg, fun i x hx => ?_⟩
  change ‖iteratedFDeriv ℝ m (f i - g i) x‖ ≤ Cf + Cg
  rw [iteratedFDeriv_sub_apply
    (((hcf i x hx).contDiffAt (hs.mem_nhds hx)).of_le (by exact_mod_cast le_top))
    (((hcg i x hx).contDiffAt (hs.mem_nhds hx)).of_le (by exact_mod_cast le_top))]
  exact (norm_sub_le _ _).trans (add_le_add (hCf i x hx) (hCg i x hx))

theorem HasUniformJetBoundsOn.clm {n : ℕ} {s : Set E} (hs : IsOpen s)
    {f : ι → E → F} (hf : HasUniformJetBoundsOn n s f)
    (hcf : ∀ i, ContDiffOn ℝ ∞ (f i) s) (L : F →L[ℝ] G) :
    HasUniformJetBoundsOn n s (fun i x => L (f i x)) := by
  intro m hm
  obtain ⟨C, hC⟩ := hf m hm
  refine ⟨‖L‖ * C, fun i x hx => ?_⟩
  exact (L.norm_iteratedFDeriv_comp_left ((hcf i x hx).contDiffAt (hs.mem_nhds hx))
    (by exact_mod_cast le_top : (m : ℕ∞ω) ≤ ∞)).trans
      (mul_le_mul_of_nonneg_left (hC i x hx) (norm_nonneg L))

theorem HasUniformJetBoundsOn.bilinear {n : ℕ} {s : Set E} (hs : IsOpen s)
    {f : ι → E → F} {g : ι → E → G}
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (hf : HasUniformJetBoundsOn n s f) (hg : HasUniformJetBoundsOn n s g)
    (hcf : ∀ i, ContDiffOn ℝ ∞ (f i) s) (hcg : ∀ i, ContDiffOn ℝ ∞ (g i) s)
    (B : F →L[ℝ] G →L[ℝ] H) :
    HasUniformJetBoundsOn n s (fun i x => B (f i x) (g i x)) := by
  obtain ⟨Cf, hCf0, hCf⟩ := bound_all_orders hf
  obtain ⟨Cg, hCg0, hCg⟩ := bound_all_orders hg
  intro m hm
  refine ⟨‖B‖ * ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * Cf * Cg,
    fun i x hx => ?_⟩
  have hb := B.norm_iteratedFDerivWithin_le_of_bilinear
    (hcf i) (hcg i) hs.uniqueDiffOn hx (by exact_mod_cast le_top : (m : ℕ∞ω) ≤ ∞)
  simp only [iteratedFDerivWithin_of_isOpen _ hs hx] at hb
  refine hb.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_) (norm_nonneg B))
  have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  gcongr
  · exact hCf j (hjm.trans hm) i x hx
  · exact hCg (m - j) ((Nat.sub_le _ _).trans hm) i x hx

theorem HasUniformJetBoundsOn.clm_comp {n : ℕ} {s : Set E} (hs : IsOpen s)
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : ι → E → G →L[ℝ] H} {g : ι → E → F →L[ℝ] G}
    (hf : HasUniformJetBoundsOn n s f) (hg : HasUniformJetBoundsOn n s g)
    (hcf : ∀ i, ContDiffOn ℝ ∞ (f i) s) (hcg : ∀ i, ContDiffOn ℝ ∞ (g i) s) :
    HasUniformJetBoundsOn n s (fun i x => (f i x).comp (g i x)) :=
  hf.bilinear hs hg hcf hcg (ContinuousLinearMap.compL ℝ F G H)

end PoincareConjecture.CoordinateTransition
