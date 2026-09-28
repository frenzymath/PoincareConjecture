import PoincareConjecture.Proofs.M10.SmoothMetric

set_option autoImplicit false

open Bundle ContinuousLinearMap Filter Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ}

set_option backward.isDefEq.respectTransparency false in

theorem backwardMetricCoordinates_continuousWithinAt_zero
    (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J) (p : M) :
    ContinuousWithinAt (backwardMetricCoordinates F T p)
      (univ ×ˢ Icc 0 τmax) (p, 0) := by
  have hm := F.smooth.continuousOn (T, p) ⟨hT, mem_univ p⟩
  rw [continuousWithinAt_hom_bundle] at hm
  have hc := hm.2
  have hc' : ContinuousWithinAt
      (fun z : ℝ × M ↦ inCoordinates (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n))
        (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (fun q ↦ TangentSpace (𝓡 n) q →L[ℝ] ℝ)
        p z.2 p z.2 ((F.metric z.1).inner z.2))
      (J ×ˢ univ) (T - (0 : ℝ), p) := by
    simpa only [sub_zero] using hc
  apply hc'.comp (x := (p, 0))
    ((continuousAt_const.sub continuousAt_snd).prodMk continuousAt_fst).continuousWithinAt
  intro z hz
  refine ⟨hwindow ?_, mem_univ _⟩
  change T - τmax ≤ T - z.2 ∧ T - z.2 ≤ T
  constructor <;> linarith [hz.2.1, hz.2.2]

end PoincareConjecture.M10
