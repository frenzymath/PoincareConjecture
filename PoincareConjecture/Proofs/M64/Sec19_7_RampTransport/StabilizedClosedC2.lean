import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.BoundaryBootstrapAnnulusChart
import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.BoundaryBootstrapStripC2
import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.StabilizedComparisonError





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M64.RampTransport

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}
  {P : M62.CircleProductData F circumference}
  {Q : M62.CircleProductData P.flow auxiliary} {time : ℝ}
  {gamma0 gamma1 : ℝ → P.charts.Point}
  {A : M64Annulus (P.flow.metric time) gamma0 gamma1} {r epsilon : ℝ}




theorem stabilized_minimum_closed_c2
    (S : StabilizedSmoothRampApproximation P Q time gamma0 gamma1 A r epsilon) :
    ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) 2 S.separated.minimum.map
      {p : LoopPlane | p 1 ∈ Icc (0 : ℝ) 1} := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  let : Fact (0 < auxiliary) := ⟨Q.circle.positive⟩
  apply annulus_strip_c2_of_boundary_charts S.separated.minimum.map
    S.separated.modulus_pos.ne' S.separated.interior_smooth
  intro x upper
  cases upper
  · exact annulus_strip_boundary_coordinate_c2 S.separated.minimum S.separated.modulus_pos
      x false (stabilized_minimum_area_minimizing S) S.separated.closed_c1
      S.separated.interior_smooth S.separated.conformal
      (fun p hp => (S.separated.within_immersion p hp).2.2)
      S.lower_smooth S.lower_immersed S.separated.first_label_c1
      S.separated.minimum.lower_boundary
  · exact annulus_strip_boundary_coordinate_c2 S.separated.minimum S.separated.modulus_pos
      x true (stabilized_minimum_area_minimizing S) S.separated.closed_c1
      S.separated.interior_smooth S.separated.conformal
      (fun p hp => (S.separated.within_immersion p hp).2.2)
      S.upper_smooth S.upper_immersed S.separated.second_label_c1
      S.separated.minimum.upper_boundary

end PoincareConjecture.M64.RampTransport
