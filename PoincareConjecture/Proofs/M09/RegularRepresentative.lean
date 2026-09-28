import PoincareConjecture.Proofs.M09.ExponentialAction
import Mathlib.Geometry.Manifold.Algebra.LieGroup

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_regular_representative_smooth {J : Set ℝ} {F : RicciFlow n M J}
    (hM04 : RicciFlowCurvatureTheory.{u}) {T τmax : ℝ}
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    {p : M} (A : LExponentialFamily F T τmax p)
    (G : OpenPartialHomeomorph (TangentSpace (𝓡 n) p × ℝ) (M × ℝ))
    (htarget : G.target ⊆ Set.univ ×ˢ Set.Ioo 0 τmax)
    (hinv : letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
      ContMDiffOn ((𝓡 n).prod (𝓘(ℝ, ℝ)))
        ((𝓘(ℝ, TangentSpace (𝓡 n) p)).prod (𝓘(ℝ, ℝ))) ∞ G.symm G.target) :
    ContMDiffOn ((𝓡 n).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, ℝ)) ∞
      (fun w ↦ A.action (G.symm w).1 w.2 / (2 * Real.sqrt w.2)) G.target := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  intro w hw
  have ht := (htarget hw).2
  have haction : ContDiffAt ℝ ∞
      (fun v : TangentSpace (𝓡 n) p × ℝ ↦ A.action v.1 v.2) ((G.symm w).1, w.2) :=
    (lExponentialFamily_action_contDiffOn hM04 hτmax hwindow A).contDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨Set.mem_univ _, ht⟩)
  have hmap : ContMDiffAt ((𝓡 n).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, TangentSpace (𝓡 n) p × ℝ)) ∞
      (fun z : M × ℝ ↦ ((G.symm z).1, z.2)) w := by
    convert! (hinv.contMDiffAt (G.open_target.mem_nhds hw)).fst.prodMk contMDiffAt_snd using 1 <;>
      simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have hnum := haction.contMDiffAt.comp w hmap
  have hroot : ContMDiffAt ((𝓡 n).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, ℝ)) ∞
      (fun z : M × ℝ ↦ Real.sqrt z.2) w :=
    (Real.contDiffAt_sqrt ht.1.ne').contMDiffAt.comp w contMDiffAt_snd
  exact (hnum.div₀ (contMDiffAt_const.mul hroot)
    (mul_ne_zero two_ne_zero (Real.sqrt_pos.mpr ht.1).ne')).contMDiffWithinAt

end PoincareConjecture.Proofs.M09
