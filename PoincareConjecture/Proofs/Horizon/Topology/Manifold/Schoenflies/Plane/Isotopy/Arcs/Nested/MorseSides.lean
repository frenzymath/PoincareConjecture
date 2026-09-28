import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Nested.RibbonRegion
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Resolution.Ribbon








noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Nested

open SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)




theorem exists_filled_coincidence_of_nested_negative_morse_arcs
    (A B : Fin 2 → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hA : A 1 '' closedBall 0 1 ⊆ A 0 '' ball 0 1)
    (hB : B 1 '' closedBall 0 1 ⊆ B 0 '' ball 0 1)
    {r t w : Real} (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2)
    (hwr : w ≤ hyperbolaRadius r t)
    (hedge : ∀ i : Fin 2, ∀ s ∈ Ioo (-w) w,
      negativeLevelRibbon t (WithLp.toLp 2 ![s, (i : Real)]) ∈
        (A i '' sphere (0 : E2) 1) ∩ (B i '' sphere (0 : E2) 1))
    (hAlevel : ∀ x ∈ openSquare r,
      x ∈ (A 0 '' sphere (0 : E2) 1) ∪ (A 1 '' sphere (0 : E2) 1) →
      -(x 0)^2 + (x 1)^2 = -t)
    (hBlevel : ∀ x ∈ openSquare r,
      x ∈ (B 0 '' sphere (0 : E2) 1) ∪ (B 1 '' sphere (0 : E2) 1) →
      -(x 0)^2 + (x 1)^2 = -t) :
    ∀ i : Fin 2, ∃ V : Set E2, IsOpen V ∧
      (fun s : Real => negativeLevelRibbon t (WithLp.toLp 2 ![s, (i : Real)])) ''
        Ioo (-w) w ⊆ V ∧
      V ∩ (A i '' closedBall 0 1) = V ∩ (B i '' closedBall 0 1) ∧
      V ∩ (A i '' ball 0 1) = V ∩ (B i '' ball 0 1) := by
  apply exists_filled_coincidence_of_shared_nested_ribbon A B hA hB
    (negativeLevelRibbonDiffeomorph ht) hedge
  intro s hs
  apply disjoint_left.mpr
  rintro x ⟨u, hu, rfl⟩ hx
  have hs' : s ∈ Ioo (-hyperbolaRadius r t) (hyperbolaRadius r t) :=
    ⟨(neg_le_neg hwr).trans_lt hs.1, hs.2.trans_le hwr⟩
  have hsq := negativeLevelRibbon_mem_openSquare hr ht htr
    (z := WithLp.toLp 2 ![s, u]) (by simpa using hs')
    (by simpa using Ioo_subset_Icc_self hu)
  have hheight := negativeLevelRibbon_height_gt ht
    (z := WithLp.toLp 2 ![s, u]) (by simpa using hu)
  have heq : -(negativeLevelRibbon t (WithLp.toLp 2 ![s, u]) 0)^2 +
      (negativeLevelRibbon t (WithLp.toLp 2 ![s, u]) 1)^2 = -t := by
    rcases hx with hx | hx
    · exact hAlevel _ hsq hx
    · exact hBlevel _ hsq hx
  exact (ne_of_gt hheight) heq

end Poincare.Manifold.Schoenflies.PlaneArcs.Nested
