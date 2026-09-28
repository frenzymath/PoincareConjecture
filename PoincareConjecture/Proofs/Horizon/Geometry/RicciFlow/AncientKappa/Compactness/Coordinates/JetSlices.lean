import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SpatialJets
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.UniformSpace.UniformConvergence













set_option autoImplicit false

open Set Filter Metric
open scoped Topology ContDiff Pointwise

namespace PoincareConjecture.AncientCompactness

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {x₀ : E}

private theorem uniqueDiffOn_spatial_closedBall {ρ : ℝ} (hρ : 0 < ρ) :
    UniqueDiffOn ℝ (closedBall x₀ ρ) := by
  apply uniqueDiffOn_convex (convex_closedBall x₀ ρ)
  rw [interior_closedBall x₀ hρ.ne']
  exact ⟨x₀, by simpa using hρ⟩



theorem iteratedFDeriv_spatial_slice_of_centered_halfCylinder
    {ρ : ℝ} (hρ : 0 < ρ) (f : ℝ × E → F)
    (hf : ContDiffOn ℝ ∞ f (Iic 0 ×ˢ closedBall x₀ ρ))
    {t : ℝ} (ht : t ≤ 0) {x : E} (hx : x ∈ ball x₀ ρ) (r : ℕ) :
    iteratedFDeriv ℝ r (fun y => f (t, y)) x =
      (iteratedFDerivWithin ℝ r f (Iic 0 ×ˢ closedBall x₀ ρ) (t, x)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ ℝ E) := by
  let a : ℝ × E := (t, 0)
  let ι : E →L[ℝ] ℝ × E := ContinuousLinearMap.inr ℝ ℝ E
  let S : Set (ℝ × E) := Iic (-t) ×ˢ closedBall x₀ ρ
  have hball := uniqueDiffOn_spatial_closedBall (x₀ := x₀) hρ
  have hS : UniqueDiffOn ℝ S := (uniqueDiffOn_Iic (-t)).prod hball
  have hpre : ι ⁻¹' S = closedBall x₀ ρ := by
    ext y
    simp [ι, S, neg_nonneg.mpr ht]
  have hshift : ContDiffOn ℝ ∞ (fun z : ℝ × E => f (a + z)) S := by
    apply hf.comp (contDiff_const.add contDiff_id).contDiffOn
    intro z hz
    refine ⟨?_, by simpa [a] using hz.2⟩
    change t + z.1 ≤ 0
    have hztime : z.1 ≤ -t := hz.1
    linarith
  have hιx : ι x ∈ S := by
    exact ⟨neg_nonneg.mpr ht, ball_subset_closedBall hx⟩
  have hr : (r : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr (le_top : (r : ℕ∞) ≤ ⊤)
  have hcomp := ι.iteratedFDerivWithin_comp_right hshift hS
    (hpre ▸ hball) hιx hr
  have hset : a +ᵥ S = Iic 0 ×ˢ closedBall x₀ ρ := by
    ext z
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simp only [S, a, mem_prod, mem_Iic, Prod.fst_add, Prod.fst_neg,
      Prod.snd_add, Prod.snd_neg, neg_zero, zero_add, vadd_eq_add]
    constructor <;> intro hz <;> exact ⟨by linarith [hz.1], hz.2⟩
  have hslice : ContDiffOn ℝ ∞ (fun y => f (t, y)) (closedBall x₀ ρ) := by
    exact hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun y hy => ⟨ht, hy⟩)
  have hsliceAt := hslice.contDiffAt
    (mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall)
  rw [hpre] at hcomp
  rw [iteratedFDerivWithin_comp_add_left, hset] at hcomp
  simpa [a, ι, Function.comp_def,
    iteratedFDerivWithin_eq_iteratedFDeriv hball (hsliceAt.of_le hr)
      (ball_subset_closedBall hx)] using hcomp



theorem derivWithin_time_slice_of_centered_halfCylinder
    {ρ : ℝ} (hρ : 0 < ρ) (f : ℝ × E → F)
    (hf : ContDiffOn ℝ ∞ f (Iic 0 ×ˢ closedBall x₀ ρ))
    {t : ℝ} (ht : t ≤ 0) {x : E} (hx : x ∈ closedBall x₀ ρ) :
    derivWithin (fun s => f (s, x)) (Iic 0) t =
      iteratedFDerivWithin ℝ 1 f (Iic 0 ×ˢ closedBall x₀ ρ) (t, x)
        (fun _ => (1, 0)) := by
  have hu := (uniqueDiffOn_Iic 0).prod (uniqueDiffOn_spatial_closedBall (x₀ := x₀) hρ)
  have hd := (hf (t, x) ⟨ht, hx⟩).differentiableWithinAt (by simp)
  have hs : HasDerivWithinAt (fun s : ℝ => (s, x)) (1, 0) (Iic 0) t :=
    (hasDerivWithinAt_id t (Iic 0)).prodMk (hasDerivWithinAt_const t (Iic 0) x)
  have hmap : MapsTo (fun s : ℝ => (s, x)) (Iic 0) (Iic 0 ×ˢ closedBall x₀ ρ) :=
    fun s hs => ⟨hs, hx⟩
  have hc := hd.hasFDerivWithinAt.comp_hasDerivWithinAt t hs hmap
  simpa only [Function.comp_def, iteratedFDerivWithin_one_apply (hu (t, x) ⟨ht, hx⟩)]
    using hc.derivWithin (uniqueDiffOn_Iic 0 t ht)



theorem tendsto_spatial_slice_jet_of_centered_halfCylinder
    {α : Type*} {l : Filter α} {ρ : ℝ} (hρ : 0 < ρ)
    (fseq : α → ℝ × E → F) (f : ℝ × E → F)
    (hseq : ∀ k, ContDiffOn ℝ ∞ (fseq k) (Iic 0 ×ˢ closedBall x₀ ρ))
    (hf : ContDiffOn ℝ ∞ f (Iic 0 ×ˢ closedBall x₀ ρ))
    {t : ℝ} (ht : t ≤ 0) {x : E} (hx : x ∈ ball x₀ ρ) (r : ℕ)
    (h : Tendsto (fun k => iteratedFDerivWithin ℝ r (fseq k)
      (Iic 0 ×ˢ closedBall x₀ ρ) (t, x)) l
      (𝓝 (iteratedFDerivWithin ℝ r f (Iic 0 ×ˢ closedBall x₀ ρ) (t, x)))) :
    Tendsto (fun k => iteratedFDeriv ℝ r (fun y => fseq k (t, y)) x) l
      (𝓝 (iteratedFDeriv ℝ r (fun y => f (t, y)) x)) := by
  let P := ContinuousMultilinearMap.compContinuousLinearMapL
    (𝕜 := ℝ) (F := F) (fun _ : Fin r => ContinuousLinearMap.inr ℝ ℝ E)
  simpa only [iteratedFDeriv_spatial_slice_of_centered_halfCylinder hρ _ hf ht hx,
    iteratedFDeriv_spatial_slice_of_centered_halfCylinder hρ _ (hseq _) ht hx, Function.comp_def,
    P, ContinuousMultilinearMap.compContinuousLinearMapL_apply]
    using P.continuous.continuousAt.tendsto.comp h



theorem tendsto_derivWithin_time_slice_of_centered_halfCylinder
    {α : Type*} {l : Filter α} {ρ : ℝ} (hρ : 0 < ρ)
    (fseq : α → ℝ × E → F) (f : ℝ × E → F)
    (hseq : ∀ k, ContDiffOn ℝ ∞ (fseq k) (Iic 0 ×ˢ closedBall x₀ ρ))
    (hf : ContDiffOn ℝ ∞ f (Iic 0 ×ˢ closedBall x₀ ρ))
    {t : ℝ} (ht : t ≤ 0) {x : E} (hx : x ∈ closedBall x₀ ρ)
    (h : Tendsto (fun k => iteratedFDerivWithin ℝ 1 (fseq k)
      (Iic 0 ×ˢ closedBall x₀ ρ) (t, x)) l
      (𝓝 (iteratedFDerivWithin ℝ 1 f (Iic 0 ×ˢ closedBall x₀ ρ) (t, x)))) :
    Tendsto (fun k => derivWithin (fun s => fseq k (s, x)) (Iic 0) t) l
      (𝓝 (derivWithin (fun s => f (s, x)) (Iic 0) t)) := by
  simpa only [derivWithin_time_slice_of_centered_halfCylinder hρ _ hf ht hx,
    derivWithin_time_slice_of_centered_halfCylinder hρ _ (hseq _) ht hx, Function.comp_def]
    using (continuous_eval_const (fun _ : Fin 1 => (1, (0 : E)))).continuousAt.tendsto.comp h

end PoincareConjecture.AncientCompactness
