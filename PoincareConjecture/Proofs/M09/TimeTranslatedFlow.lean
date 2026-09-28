import PoincareConjecture.Definitions.Ch03.RicciFlow
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace








set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

noncomputable def timeTranslatedFlow {J : Set ℝ} (F : RicciFlow n M J)
    (a L : ℝ) (hL : 0 < L)
    (hwindow : ∀ t ∈ Set.Icc 0 L, a + t ∈ J) : RicciFlow n M (Set.Icc 0 L) where
  metric t := F.metric (a + t)
  connection t := F.connection (a + t)
  interval := Set.ordConnected_Icc
  nontrivial := ⟨0, ⟨le_rfl, hL.le⟩, L, ⟨hL.le, le_rfl⟩, ne_of_lt hL⟩
  smooth := by
    have ht : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ∞
        (fun z : ℝ × M ↦ (a + z.1, z.2)) :=
      (((contDiff_const.add contDiff_id).contMDiff).comp contMDiff_fst).prodMk contMDiff_snd
    exact F.smooth.comp ht.contMDiffOn (fun z hz ↦ ⟨hwindow z.1 hz.1, Set.mem_univ _⟩)
  equation t ht x v w := by
    have hshift : HasDerivWithinAt (fun s : ℝ ↦ a + s) 1 (Set.Icc 0 L) t :=
      ((hasDerivAt_id t).const_add a).hasDerivWithinAt
    simpa only [Function.comp_def, mul_one] using
      (F.equation (a + t) (hwindow t ht) x v w).comp t hshift hwindow

end PoincareConjecture.Proofs.M09
