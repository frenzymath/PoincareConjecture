import PoincareConjecture.Proofs.M76.PrimeReduction.BoundaryVertexHalfBall
import PoincareConjecture.Proofs.M76.PrimeReduction.ConvexHalfBodyDisks









set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

local notation "V3" => (Fin 3 → ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {K L : SimplicialComplex ℝ E} [Fintype K.faces] [Fintype L.faces] {p : E}



theorem BoundaryVertexHalfBall.boundary_disks (H : BoundaryVertexHalfBall K L p) :
    IsFinitePLBallPair (ℝ × ℝ) ((K.barycentricDualBlock {p}).link p).space
        (((K.barycentricDualBlock {p}).link p).space ∩ (L.barycentricDualBlock {p}).space) ∧
      IsFinitePLBallPair (ℝ × ℝ) (L.barycentricDualBlock {p}).space
        (((K.barycentricDualBlock {p}).link p).space ∩ (L.barycentricDualBlock {p}).space) := by
  classical
  let N := K.barycentricDualBlock {p}
  let B := (N.link p).space
  let W := (L.barycentricDualBlock {p}).space
  let U := frontier H.body ∩ {x | 0 ≤ H.height x}
  let Z := H.body ∩ {x | H.height x = 0}
  obtain ⟨J, hJ, hJC⟩ := H.polyhedral
  obtain ⟨hU, hZ⟩ := J.isFinitePLBallPair_convex_half_body_sides
    hJ H.compact H.convex H.center hJC H.height H.normal H.normalized
    (F := ℝ × ℝ) (by simp [Module.finrank_prod])
  have hBN : B ⊆ N.space := fun _ hx => H.ball.1 (Or.inl hx)
  have hWN : W ⊆ N.space := fun _ hx => H.ball.1 (Or.inr hx)
  have hUT : U ⊆ H.body ∩ {x | 0 ≤ H.height x} :=
    fun _ hx => ⟨H.compact.isClosed.frontier_subset hx.1, hx.2⟩
  have hZT : Z ⊆ H.body ∩ {x | 0 ≤ H.height x} :=
    fun _ hx => ⟨hx.1, hx.2.ge⟩
  have hmemB (x : N.space) : (x : E) ∈ B ↔ (H.chart x : V3) ∈ U := by
    exact (H.link x).trans (and_iff_left (H.chart x).property.2).symm
  have hmemW (x : N.space) : (x : E) ∈ W ↔ (H.chart x : V3) ∈ Z := by
    constructor
    · intro hx
      exact ⟨(H.chart x).property.1, (H.boundary x).mpr hx⟩
    · intro hx
      exact (H.boundary x).mp hx.2
  let GB := H.chart.restrictSubsets hBN hUT hmemB
  let GW := H.chart.restrictSubsets hWN hZT hmemW
  have hGB : GB.IsFinitePL := H.piecewiseAffine.restrictSubsets hBN hUT hmemB
    (N.link p) (finite_link_faces (K.barycentricDualBlock_finite {p}) p) rfl
  have hGW : GW.IsFinitePL := H.piecewiseAffine.restrictSubsets hWN hZT hmemW
    (L.barycentricDualBlock {p}) (L.barycentricDualBlock_finite {p}) rfl
  constructor
  · apply hU.of_homeomorph inter_subset_left GB hGB
    intro x
    change ((x : E) ∈ B ∧ (x : E) ∈ W) ↔
      (H.chart ⟨x, hBN x.property⟩ : V3) ∈ frontier H.body ∧
        H.height (H.chart ⟨x, hBN x.property⟩ : V3) = 0
    rw [and_iff_right x.property,
      and_iff_right ((H.link ⟨x, hBN x.property⟩).mp x.property)]
    exact (H.boundary ⟨x, hBN x.property⟩).symm
  · apply hZ.of_homeomorph inter_subset_right GW hGW
    intro x
    change ((x : E) ∈ B ∧ (x : E) ∈ W) ↔
      (H.chart ⟨x, hWN x.property⟩ : V3) ∈ frontier H.body ∧
        H.height (H.chart ⟨x, hWN x.property⟩ : V3) = 0
    rw [and_iff_left x.property,
      and_iff_left ((H.boundary ⟨x, hWN x.property⟩).mpr x.property)]
    exact H.link ⟨x, hWN x.property⟩

end Geometry.SimplicialComplex
