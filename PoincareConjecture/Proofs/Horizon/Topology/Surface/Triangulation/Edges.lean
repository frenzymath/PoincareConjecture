


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Basic








set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M]


def affineChartSegment (a b : EuclideanSpace ℝ (Fin 2)) : ℝ → EuclideanSpace ℝ (Fin 2) :=
  fun t => a + t • (b - a)



theorem exists_smoothEdge_of_affineChartSegment
    (p : M) {a b : EuclideanSpace ℝ (Fin 2)} (hab : a ≠ b)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1,
      affineChartSegment a b t ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) p).target) :
    ∃ e : SmoothEdge M,
      e.map = (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm ∘ affineChartSegment a b ∧
      Set.InjOn e.map (Icc (0 : ℝ) 1) ∧
      e.map 0 = (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm a ∧
      e.map 1 = (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm b := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hsm : ContDiff ℝ ∞ (affineChartSegment a b) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hd (t : ℝ) : HasFDerivAt (affineChartSegment a b)
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (b - a)) t := by
    exact ((hasFDerivAt_id t).smul_const (b - a)).const_add a
  have hinj : Function.Injective (affineChartSegment a b) := by
    intro s t h
    exact smul_left_injective ℝ hba (add_left_cancel h)
  let e : SmoothEdge M := {
    map := (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm ∘ affineChartSegment a b
    smooth := (contMDiffOn_chart_symm (I := 𝓡 2) (x := p)).comp
      hsm.contMDiff.contMDiffOn hseg
    regular := by
      intro t ht
      have htarget := hseg t ⟨ht.1.le, ht.2.le⟩
      rw [mfderiv_comp t
        ((mdifferentiable_chart (I := 𝓡 2) p).mdifferentiableAt_symm htarget)
        (hd t).differentiableAt.mdifferentiableAt, mfderiv_eq_fderiv, (hd t).fderiv]
      exact ((mdifferentiable_chart (I := 𝓡 2) p).symm.mfderiv_injective htarget).comp
        (smul_left_injective ℝ hba) }
  refine ⟨e, rfl, ?_, ?_, ?_⟩
  · intro s hs t ht h
    exact hinj ((chartAt (EuclideanSpace ℝ (Fin 2)) p).symm.injOn
      (hseg s hs) (hseg t ht) h)
  · simp [e, affineChartSegment]
  · simp [e, affineChartSegment]

end PoincareConjecture.Topology.Surface
