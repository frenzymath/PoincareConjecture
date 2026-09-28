import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionFrontier
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.VertexContributions

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology ContDiff Manifold Bundle
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

private theorem sum_endpoint_degree
    {V E : Type*} [Fintype V] [Fintype E] (ends : E → V × V)
    (hdistinct : ∀ e, (ends e).1 ≠ (ends e).2) :
    (∑ v : V, (Nat.card {e : E // (ends e).1 = v ∨ (ends e).2 = v} : ℝ)) =
      2 * Fintype.card E := by
  classical
  have hdegree (v : V) :
      (Nat.card {e : E // (ends e).1 = v ∨ (ends e).2 = v} : ℝ) =
        ∑ e : E, ((if (ends e).1 = v then (1 : ℝ) else 0) +
          if (ends e).2 = v then 1 else 0) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hleft : (ends e).1 = v
    · have hright : (ends e).2 ≠ v := fun h => hdistinct e (hleft.trans h.symm)
      simp only [hleft, hright, true_or, if_true, if_false, add_zero]
    · by_cases hright : (ends e).2 = v <;> simp only [hleft, hright, false_or,
        if_true, if_false, zero_add]
  simp_rw [hdegree]
  rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

theorem m64Intrinsic_region_boundary_degree_sum
    {I : Type*} [Finite I] (face : I → SmoothFace AnnulusCoordinates)
    (F : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source) :
    let _ := Fintype.ofFinite (Euler.CoordinateVertex F b)
    (∑ v : Euler.CoordinateVertex F b, (Nat.card {e :
        {e : FaceBoundaryEdge face // Nat.card {p : I × Fin 3 //
          faceBoundaryIndex face p.1 p.2 = e} = 1} //
      (Euler.coordinateEdgeEnds face F b e.1).1 = v ∨
        (Euler.coordinateEdgeEnds face F b e.1).2 = v} : ℝ)) =
      2 * Nat.card {e : FaceBoundaryEdge face // Nat.card {p : I × Fin 3 //
        faceBoundaryIndex face p.1 p.2 = e} = 1} := by
  classical
  let _ := Fintype.ofFinite (Euler.CoordinateVertex F b)
  let E := {e : FaceBoundaryEdge face // Nat.card {p : I × Fin 3 //
    faceBoundaryIndex face p.1 p.2 = e} = 1}
  let _ := Fintype.ofFinite E
  simpa only [Nat.card_eq_fintype_card] using sum_endpoint_degree
    (fun e : E => Euler.coordinateEdgeEnds face F b e.1)
    (fun e => Euler.coordinateEdgeEnds_distinct face F b hsource e.1)

open Classical in

theorem m64Intrinsic_region_gaussBonnet_euler
    {I : Type*} [Fintype I] (face : I → SmoothFace AnnulusCoordinates)
    (F : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hF : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i) (F i).source)
    (hFi : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i).symm (F i).target)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
    (hcarrier : ∀ i, (face i).carrier = F i '' convexHull ℝ (range (b i)))
    (hboundary : ∀ i k, ((face i).boundary k).map = F i ∘
      affineChartSegment (b i (k.succAbove 0)) (b i (k.succAbove 1)))
    (hfront : ∀ i j, i ≠ j → (face i).carrier ∩ (face j).carrier ⊆ frontier (face i).carrier)
    {g : RiemannianMetric 2 AnnulusCoordinates} (D : LeviCivitaData g)
    (Q : ∀ i, RiemannianMetric.AlignedChartFrame g (coordinateTriangleChart (F i) (b i))) :
    let _ := Fintype.ofFinite (Euler.CoordinateVertex F b)
    (∫ x in ⋃ i, (face i).carrier, D.scalarCurvature x ∂g.volumeMeasure) +
      2 * (∑ p : I × Fin 3, if ∀ q : I × Fin 3,
          faceBoundaryIndex face q.1 q.2 = faceBoundaryIndex face p.1 p.2 → q = p then
        coordinateTriangleTurningIntegral D (F p.1) (b p.1) (Q p.1) (p.2 + 1) ((p.2 + 1) + 1)
        else 0) +
      2 * (∑ v : Euler.CoordinateVertex F b,
        ((2 - (Nat.card {e : {e : FaceBoundaryEdge face //
          Nat.card {p : I × Fin 3 // faceBoundaryIndex face p.1 p.2 = e} = 1} //
            (Euler.coordinateEdgeEnds face F b e.1).1 = v ∨
              (Euler.coordinateEdgeEnds face F b e.1).2 = v} : ℝ) / 2) * Real.pi -
          coordinateVertexAngleContribution g F b v.1)) =
      4 * Real.pi * ((Nat.card (Euler.CoordinateVertex F b) : ℝ) -
        Nat.card (FaceBoundaryEdge face) + Nat.card I) := by
  classical
  let _ := Fintype.ofFinite (Euler.CoordinateVertex F b)
  let E := {e : FaceBoundaryEdge face // Nat.card {p : I × Fin 3 //
    faceBoundaryIndex face p.1 p.2 = e} = 1}
  let degree (v : Euler.CoordinateVertex F b) : ℝ := Nat.card {e : E //
    (Euler.coordinateEdgeEnds face F b e.1).1 = v ∨
      (Euler.coordinateEdgeEnds face F b e.1).2 = v}
  have hdegrees : (∑ v, degree v) = 2 * Nat.card E :=
    m64Intrinsic_region_boundary_degree_sum face F b hsource
  have hslots : 3 * (Nat.card I : ℝ) + Nat.card E =
      2 * Nat.card (FaceBoundaryEdge face) := by
    exact_mod_cast m64Intrinsic_region_edge_slot_count face F b hsource hcarrier hboundary hfront
  have hangles := sum_coordinateVertexAngleContribution g F b
  have hcorners : (∑ i, ∑ k : Fin 3, (Real.pi - coordinateTriangleAngle g (F i) (b i) k)) =
      3 * Real.pi * Nat.card I - ∑ i, ∑ k : Fin 3, coordinateTriangleAngle g (F i) (b i) k := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.card_eq_fintype_card]
    ring
  have hdefects : (∑ v : Euler.CoordinateVertex F b,
      ((2 - degree v / 2) * Real.pi - coordinateVertexAngleContribution g F b v.1)) =
      2 * Real.pi * Nat.card (Euler.CoordinateVertex F b) - Real.pi * Nat.card E -
        ∑ i, ∑ k : Fin 3, coordinateTriangleAngle g (F i) (b i) k := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib,
      ← Finset.sum_div, hdegrees, hangles]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
    ring
  have hgb := m64Intrinsic_region_gaussBonnet_unpaired face F b hF hFi hsource
    hcarrier hboundary hfront D Q
  rw [hcorners] at hgb
  change _ + 2 * (∑ v : Euler.CoordinateVertex F b,
    ((2 - degree v / 2) * Real.pi - coordinateVertexAngleContribution g F b v.1)) = _
  rw [hdefects]
  have hcard : (Fintype.card I : ℝ) = Nat.card I := by rw [Nat.card_eq_fintype_card]
  rw [hcard] at hgb
  nlinarith [congrArg (fun x : ℝ => Real.pi * x) hslots]

end PoincareConjecture
