import PoincareConjecture.Proofs.M47.CanonicalTensorFamilyNorm
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_RoundPullback









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.Proofs.M47

variable {n : ℕ} {M : Type u} {X : Type v} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ X]
  {J : Set ℝ} {U : Set X}



theorem contMDiffOn_flow_metricPullback_onFields (F : RicciFlow n M J)
    {f : X → M} (hf : ContMDiff (𝓡 n) (𝓡 n) ∞ f)
    (hU : IsOpen U) (Y : Fin 2 → (y : X) → TangentSpace (𝓡 n) y)
    (hY : ∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% (Y i)) U) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × X ↦ (F.metric p.1).inner (f p.2)
        (mfderiv (𝓡 n) (𝓡 n) f p.2 (Y 0 p.2))
        (mfderiv (𝓡 n) (𝓡 n) f p.2 (Y 1 p.2))) (J ×ˢ U) := by
  let E := EuclideanSpace ℝ (Fin n)
  have hZ (i : Fin 2) : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (fun y ↦ Bundle.TotalSpace.mk' E (f y)
        (mfderiv (𝓡 n) (𝓡 n) f y (Y i y))) U := by
    intro y hy
    exact (((hf y).mfderiv_const (m := ∞) (by simp)).clm_apply_of_inCoordinates
      ((hY i).contMDiffAt (hU.mem_nhds hy)) (hf y)).contMDiffWithinAt
  have hZtime (i : Fin 2) : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (fun p : ℝ × X ↦ Bundle.TotalSpace.mk' E (f p.2)
        (mfderiv (𝓡 n) (𝓡 n) f p.2 (Y i p.2))) (J ×ˢ U) :=
    (hZ i).comp contMDiffOn_snd (fun _ hp ↦ hp.2)
  have hmap : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun p : ℝ × X ↦ (p.1, f p.2)) :=
    contMDiff_fst.prodMk (hf.comp contMDiff_snd)
  have hm := F.smooth.comp hmap.contMDiffOn (fun p (hp : p ∈ J ×ˢ U) ↦
    ⟨hp.1, mem_univ (f p.2)⟩)
  intro p hp
  have he : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞
      (fun q : ℝ × X ↦ Bundle.TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) (f q.2)
        ((F.metric q.1).inner (f q.2)
          (mfderiv (𝓡 n) (𝓡 n) f q.2 (Y 0 q.2))
          (mfderiv (𝓡 n) (𝓡 n) f q.2 (Y 1 q.2)))) (J ×ˢ U) p :=
    (hm p hp).clm_bundle_apply₂ (hZtime 0 p hp) (hZtime 1 p hp)
  exact (Bundle.contMDiffWithinAt_totalSpace.mp he).2

end PoincareConjecture.Proofs.M47
