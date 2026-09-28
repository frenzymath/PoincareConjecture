import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.ImplicitFunction.RegularScalar
open Set Function
open scoped Topology ContDiff

namespace Poincare.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]


theorem exists_regular_level_parametrization {V : Set E} (hV : IsOpen V)
    {f g : E → ℝ} (hf : ContDiffOn ℝ ∞ f V) (hg : ContDiffOn ℝ ∞ g V)
    {a : E} (ha : a ∈ V) (hga : g a = 0)
    (hreg : Surjective (fderiv ℝ g a)) :
    let F := (fderiv ℝ g a).ker
    ∃ (W : Set E) (U : Set F) (p : F → E) (q : E → F),
      IsOpen W ∧ a ∈ W ∧ W ⊆ V ∧ IsOpen U ∧ (0 : F) ∈ U ∧
      ContDiffOn ℝ ∞ p U ∧ ContDiffOn ℝ ∞ q W ∧ p 0 = a ∧
      BijOn p U (W ∩ {x | g x = 0}) ∧
      (∀ u ∈ U, q (p u) = u) ∧
      (∀ x ∈ W, g x = 0 → p (q x) = x) ∧
      ContDiffOn ℝ ∞ (f ∘ p) U ∧
      ∀ u ∈ U, fderiv ℝ f (p u) = 0 → fderiv ℝ (f ∘ p) u = 0 := by
  dsimp only
  obtain ⟨e, hea, heV, hepoint, he, hei, hefirst, helevel⟩ :=
    exists_smooth_superlevel_chart hV hg ha hreg
  let F := (fderiv ℝ g a).ker
  let U : Set F := (fun u => ((0 : ℝ), u)) ⁻¹' e.target
  let p : F → E := fun u => e.symm (0, u)
  let q : E → F := fun x => (e x).2
  have hU : IsOpen U := e.open_target.preimage (continuous_const.prodMk continuous_id)
  have hpoint : e a = (0, 0) := by simpa [hga] using hepoint
  have h0 : (0 : F) ∈ U := by
    change (0, (0 : F)) ∈ e.target
    rw [← hpoint]
    exact e.map_source hea
  have hp : ContDiffOn ℝ ∞ p U :=
    hei.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun u hu => hu)
  have hq : ContDiffOn ℝ ∞ q e.source := contDiff_snd.comp_contDiffOn he
  have hps : MapsTo p U (e.source ∩ {x | g x = 0}) := by
    intro u hu
    refine ⟨e.map_target hu, ?_⟩
    change g (e.symm (0, u)) = 0
    rw [← hefirst _ (e.map_target hu)]
    exact congrArg Prod.fst (e.right_inv hu)
  have hqp : ∀ u ∈ U, q (p u) = u := by
    intro u hu
    exact congrArg Prod.snd (e.right_inv hu)
  have hezero : ∀ x ∈ e.source, g x = 0 → (0, (e x).2) = e x := by
    intro x hx hgx
    ext
    · exact (hefirst x hx).trans hgx |>.symm
    · rfl
  have hpq : ∀ x ∈ e.source, g x = 0 → p (q x) = x := by
    intro x hx hgx
    change e.symm (0, (e x).2) = x
    rw [hezero x hx hgx, e.left_inv hx]
  have hb : BijOn p U (e.source ∩ {x | g x = 0}) := by
    refine ⟨hps, ?_, ?_⟩
    · intro u hu v hv huv
      rw [← hqp u hu, ← hqp v hv, huv]
    · intro x hx
      refine ⟨q x, ?_, hpq x hx.1 hx.2⟩
      change (0, (e x).2) ∈ e.target
      rw [hezero x hx.1 hx.2]
      exact e.map_source hx.1
  have hpV : MapsTo p U V := fun u hu => heV (hps hu).1
  refine ⟨e.source, U, p, q, e.open_source, hea, heV, hU, h0, hp, hq,
    ?_, hb, hqp, hpq, hf.comp hp hpV, ?_⟩
  · change e.symm (0, 0) = a
    rw [← hpoint, e.left_inv hea]
  · intro u hu hcrit
    have hfu := ((hf (p u) (hpV hu)).contDiffAt
      (hV.mem_nhds (hpV hu))).differentiableAt (by simp)
    have hpu := ((hp u hu).contDiffAt (hU.mem_nhds hu)).differentiableAt (by simp)
    rw [fderiv_comp u hfu hpu, hcrit, ContinuousLinearMap.zero_comp]

end Poincare.Analysis
