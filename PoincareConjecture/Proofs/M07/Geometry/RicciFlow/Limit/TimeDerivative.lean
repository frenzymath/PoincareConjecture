import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Basic
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.Regularity








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Bundle Filter Set

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {g : ℝ → RiemannianMetric n M}


theorem IsSmoothFamilyOn.contDiffWithinAt_inner_time
    (hg : IsSmoothFamilyOn g J) {t : ℝ} (ht : t ∈ J)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    ContDiffWithinAt ℝ ∞ (fun s => (g s).inner x u v) J t := by
  let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u
  let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  have hX := FiberBundle.contMDiffAt_extend (k := ∞) (𝓡 n) (EuclideanSpace ℝ (Fin n)) u
  have hY := FiberBundle.contMDiffAt_extend (k := ∞) (𝓡 n) (EuclideanSpace ℝ (Fin n)) v
  have hX' : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.2))
      (J ×ˢ univ) (t, x) := (hX.comp (t, x) contMDiffAt_snd).contMDiffWithinAt
  have hY' : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (Y p.2))
      (J ×ˢ univ) (t, x) := (hY.comp (t, x) contMDiffAt_snd).contMDiffWithinAt
  have h := (contMDiffWithinAt_totalSpace.mp
    ((hg (t, x) ⟨ht, mem_univ x⟩).clm_bundle_apply₂
      (F₃ := ℝ) (E₃ := fun _ : M => ℝ) hX' hY')).2
  have h' := h.comp t (contMDiffWithinAt_id.prodMk contMDiffWithinAt_const)
    (show MapsTo (fun s : ℝ => (s, x)) J (J ×ˢ univ) from
      fun s hs => ⟨hs, mem_univ _⟩)
  simpa [X, Y, Function.comp_def] using h'.contDiffWithinAt


theorem IsSmoothFamilyOn.hasDerivAt_inner
    (hg : IsSmoothFamilyOn g J) (hJ : IsOpen J) {t : ℝ} (ht : t ∈ J)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    HasDerivAt (fun s => (g s).inner x u v)
      (deriv (fun s => (g s).inner x u v) t) t :=
  (((hg.contDiffWithinAt_inner_time ht x u v).contDiffAt (hJ.mem_nhds ht)).differentiableAt
    (by simp)).hasDerivAt

end PoincareConjecture.RiemannianMetric
