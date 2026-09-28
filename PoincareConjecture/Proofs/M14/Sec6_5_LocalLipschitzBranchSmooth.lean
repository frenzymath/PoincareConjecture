import PoincareConjecture.Proofs.M14.Sec6_3_ActionSmooth
import Mathlib.Geometry.Manifold.Algebra.LieGroup

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

theorem survivorInverse_actions_contMDiffOn
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) {O : Set G.Point}
    {inv : G.Point → G.Horizontal x × ℝ}
    (hinv : letI : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
        ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
      ContMDiffOn (spacetimeModel n) 𝓘(ℝ, G.Horizontal x × ℝ) ∞ inv O)
    (hmap : ∀ q ∈ O, inv q ∈ E.domain ∧ 0 < (inv q).2) :
    ContMDiffOn (spacetimeModel n) 𝓘(ℝ) ∞
      (fun q => E.action (inv q).1 (inv q).2) O ∧
    ContMDiffOn (spacetimeModel n) 𝓘(ℝ) ∞
      (fun q => E.action (inv q).1 (inv q).2 / (2 * (inv q).2)) O := by
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  have hinv' : ContMDiffOn (spacetimeModel n)
      ((𝓘(ℝ, G.Horizontal x)).prod (𝓘(ℝ, ℝ))) ∞ inv O := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact hinv
  have ha := (exponentialFamily_action_smooth hM04 hM12 E).comp hinv' hmap
  have ht := (ContinuousLinearMap.snd ℝ (G.Horizontal x) ℝ).contMDiff.comp_contMDiffOn hinv
  exact ⟨ha, ha.div₀ ((contMDiffOn_const (c := (2 : ℝ))).mul ht)
    (fun q hq => mul_ne_zero (by norm_num) (hmap q hq).2.ne')⟩

end PoincareConjecture.M14
