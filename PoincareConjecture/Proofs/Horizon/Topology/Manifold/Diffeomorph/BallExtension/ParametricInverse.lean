import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Flow.TimeDependent.JointInverse
import Mathlib.Geometry.Manifold.Diffeomorph












set_option autoImplicit false
open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold



theorem contMDiff_diffeomorph_family_symm
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : ℝ → Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
      (fun z : ℝ × M => f z.1 z.2)) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
      (fun z : ℝ × M => (f z.1).symm z.2) := by
  rintro ⟨s, p⟩
  let Φ : ℝ × M → M := fun z => f z.1 ((f s).symm z.2)
  have hΦ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ Φ :=
    hf.comp (contMDiff_fst.prodMk ((f s).symm.contMDiff.comp contMDiff_snd))
  obtain ⟨W, ψ, hW, hp, hψ, hright⟩ :=
    exists_smooth_spatial_rightInverse_near_initial
      (J := univ) (V := univ) isOpen_univ isOpen_univ
      hΦ.contMDiffOn (s := s) (mem_univ s)
      (fun y _ => (f s).apply_symm_apply y) (p := p) (mem_univ p)
  have h := (f s).symm.contMDiff.contMDiffAt.comp (s, p)
    (hψ.contMDiffAt (hW.mem_nhds hp))
  apply h.congr_of_eventuallyEq
  filter_upwards [hW.mem_nhds hp] with z hz
  apply (f z.1).injective
  exact ((f z.1).apply_symm_apply z.2).trans (hright z hz).2.2.symm

end Poincare.Manifold
