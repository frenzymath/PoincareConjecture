import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseTargetAngle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

theorem auxiliaryCircle_originalPhase_chart
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (q : Q.charts.Point)
    {z : EuclideanSpace ℝ (Fin ((n + 1) + 1))}
    (hz : z ∈ (extChartAt (𝓡 ((n + 1) + 1)) q).target) :
    ∃ (O : Set (EuclideanSpace ℝ (Fin ((n + 1) + 1))))
      (beta : EuclideanSpace ℝ (Fin ((n + 1) + 1)) → ℝ),
      IsOpen O ∧ z ∈ O ∧ O ⊆ (extChartAt (𝓡 ((n + 1) + 1)) q).target ∧
      ContDiffOn ℝ ∞ beta O ∧ ∀ y ∈ O,
        P.circle.quotient (beta y) = ((extChartAt (𝓡 ((n + 1) + 1)) q).symm y).1.2 := by
  let c := extChartAt (𝓡 ((n + 1) + 1)) q
  obtain ⟨U, beta, hU, hzU, hbeta, hquot⟩ :=
    auxiliaryCircle_originalPhase_local P Q (c.symm z)
  let O := c.target ∩ c.symm ⁻¹' U
  have hi (y : EuclideanSpace ℝ (Fin ((n + 1) + 1))) (hy : y ∈ c.target) :
      ContMDiffAt (𝓡 ((n + 1) + 1)) (𝓡 ((n + 1) + 1)) ∞ c.symm y :=
    (contMDiffOn_extChartAt_symm (n := ∞) q y hy).contMDiffAt
      ((isOpen_extChartAt_target q).mem_nhds hy)
  have hO : IsOpen O := isOpen_iff_mem_nhds.mpr fun y hy =>
    inter_mem ((isOpen_extChartAt_target q).mem_nhds hy.1)
      ((hi y hy.1).continuousAt (hU.mem_nhds hy.2))
  refine ⟨O, beta ∘ c.symm, hO, ⟨hz, hzU⟩, inter_subset_left, ?_, ?_⟩
  · intro y hy
    exact (contMDiffAt_iff_contDiffAt.mp
      (((hbeta (c.symm y) hy.2).contMDiffAt (hU.mem_nhds hy.2)).comp y
        (hi y hy.1))).contDiffWithinAt
  · intro y hy
    exact hquot (c.symm y) hy.2

end PoincareConjecture.M64
