import PoincareConjecture.Proofs.M11.OrdinaryCharts
import PoincareConjecture.Proofs.M11.FiniteDimensionalSmooth
import PoincareConjecture.Definitions.Ch03.RicciFlow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

noncomputable def ordinaryChartMetric (g : ℝ → RiemannianMetric n M) (p : M)
    (q : ℝ × EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  let c := chartAt (EuclideanSpace ℝ (Fin n)) p
  let B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    (g q.1).inner (c.symm q.2)
  let D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (𝓡 n) (𝓡 n) c.symm q.2
  B.bilinearComp D D

theorem ordinaryChartMetric_symm (g : ℝ → RiemannianMetric n M) (p : M)
    (t : ℝ) (x v w : EuclideanSpace ℝ (Fin n)) :
    ordinaryChartMetric g p (t, x) v w = ordinaryChartMetric g p (t, x) w v :=
  (g t).symm _ _ _

theorem ordinaryChartMetric_pos (g : ℝ → RiemannianMetric n M) (p : M)
    (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ spatialChartDomain p)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) :
    0 < ordinaryChartMetric g p (t, x) v v := by
  apply (g t).pos
  exact fun h ↦ hv ((spatialChartTangentEquiv p x hx).injective (h.trans (map_zero _).symm))

theorem ordinaryChartMetric_smooth (g : ℝ → RiemannianMetric n M) (J : Set ℝ)
    (hg : RiemannianMetric.IsSmoothFamilyOn g J) (p : M) :
    ContDiffOn ℝ ∞ (ordinaryChartMetric g p)
      (J ×ˢ (spatialChartDomain (n := n) p : Set (EuclideanSpace ℝ (Fin n)))) := by
  let c := chartAt (EuclideanSpace ℝ (Fin n)) p
  let S := J ×ˢ c.target
  have hc : ContMDiffOn (𝓘(ℝ).prod (𝓡 n)) (𝓡 n) ∞
      (fun q : ℝ × EuclideanSpace ℝ (Fin n) ↦ c.symm q.2) S :=
    contMDiffOn_chart_symm.comp contMDiffOn_snd (fun _ hx ↦ hx.2)
  have hmetric := hg.comp (contMDiffOn_fst.prodMk hc) (fun _ hx ↦ ⟨hx.1, mem_univ _⟩)
  have hvector (v : EuclideanSpace ℝ (Fin n)) :=
    (spatialChart_tangent_smooth p v).comp
      (contMDiffOn_snd (I := 𝓘(ℝ)) (J := 𝓡 n) (s := S)) (fun _ hx ↦ hx.2)
  have H : ContMDiffOn (𝓘(ℝ).prod (𝓡 n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) ∞
      (ordinaryChartMetric g p) S := by
    apply contMDiffOn_clm_of_apply
    intro v
    apply contMDiffOn_clm_of_apply
    intro w q hq
    have h := ContMDiffWithinAt.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := fun _ : M ↦ ℝ)
      (b := fun q : ℝ × EuclideanSpace ℝ (Fin n) ↦ c.symm q.2)
      (ψ := fun q ↦ (g q.1).inner (c.symm q.2))
      (hmetric q hq) (hvector v q hq) (hvector w q hq)
    convert! (contMDiffWithinAt_totalSpace.mp h).2 using 1
  rw [← contMDiffOn_iff_contDiffOn, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact H

end PoincareConjecture.Proofs.M11
