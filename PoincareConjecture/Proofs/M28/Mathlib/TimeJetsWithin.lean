import PoincareConjecture.Proofs.M28.Mathlib.SpatialJetsWithin
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

theorem derivWithin_time_slice_eq_within
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {J : Set ℝ} {U : Set E} {f : ℝ × E → F}
    (hJ : UniqueDiffOn ℝ J) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f (J ×ˢ U))
    {t : ℝ} (ht : t ∈ J) {x : E} (hx : x ∈ U) :
    derivWithin (fun s => f (s, x)) J t =
      iteratedFDerivWithin ℝ 1 f (J ×ˢ U) (t, x) (fun _ => (1, 0)) := by
  have hd := (hf.differentiableOn (by simp) (t, x) ⟨ht, hx⟩).hasFDerivWithinAt
  have hmap : HasDerivWithinAt (fun s : ℝ => (s, x)) (1, 0) J t :=
    (hasDerivWithinAt_id t J).prodMk (hasDerivWithinAt_const t J x)
  have h := hd.comp_hasDerivWithinAt t hmap
    (show MapsTo (fun s : ℝ => (s, x)) J (J ×ˢ U) from fun s hs => ⟨hs, hx⟩)
  change derivWithin (f ∘ fun s => (s, x)) J t = _
  rw [h.derivWithin (hJ t ht)]
  rw [iteratedFDerivWithin_one_apply ((hJ.prod hU.uniqueDiffOn) (t, x) ⟨ht, hx⟩)]

theorem TendstoUniformlyOn.derivWithin_time_slice
    {E F α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {l : Filter α} {J : Set ℝ} {U : Set E} {K : Set (ℝ × E)}
    {f : α → ℝ × E → F} {g : ℝ × E → F}
    (hjet : TendstoUniformlyOn
      (fun k => iteratedFDerivWithin ℝ 1 (f k) (J ×ˢ U))
      (iteratedFDerivWithin ℝ 1 g (J ×ˢ U)) l K)
    (hJ : UniqueDiffOn ℝ J) (hU : IsOpen U) (hK : K ⊆ J ×ˢ U)
    (hf : ∀ᶠ k in l, ContDiffOn ℝ ∞ (f k) (J ×ˢ U))
    (hg : ContDiffOn ℝ ∞ g (J ×ˢ U)) :
    TendstoUniformlyOn
      (fun k p => derivWithin (fun s => f k (s, p.2)) J p.1)
      (fun p => derivWithin (fun s => g (s, p.2)) J p.1) l K := by
  let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => ℝ × E) F
    (fun _ => (1, 0))
  have h := L.uniformContinuous.comp_tendstoUniformlyOn hjet
  apply (h.congr ?_).congr_right ?_
  · filter_upwards [hf] with k hk p hp
    exact (derivWithin_time_slice_eq_within hJ hU hk (hK hp).1 (hK hp).2).symm
  · intro p hp
    exact (derivWithin_time_slice_eq_within hJ hU hg (hK hp).1 (hK hp).2).symm
