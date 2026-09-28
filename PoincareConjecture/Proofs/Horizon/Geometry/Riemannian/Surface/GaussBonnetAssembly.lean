import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Integrability
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Area.Triangulation
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Combinatorial.Incidence

set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.LeviCivitaData

variable {S : Type u} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
  [T3Space S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
  [IsManifold (𝓡 2) ∞ S]
  {g : RiemannianMetric 2 S} (D : LeviCivitaData g)

theorem integral_scalarCurvature_le_eight_pi_of_gaussBonnet
    (χ : ℤ)
    (hGB : (∫ x, D.scalarCurvature x ∂g.volumeMeasure) = 4 * Real.pi * χ)
    (hχ : χ ≤ 2) :
    (∫ x, D.scalarCurvature x ∂g.volumeMeasure) ≤ 8 * Real.pi := by
  rw [hGB]
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have hscaled : (4 : ℝ) * Real.pi * (χ : ℝ) ≤
      (4 : ℝ) * Real.pi * (2 : ℝ) := by
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hχ) (by positivity)
  nlinarith

theorem integral_scalarCurvature_le_eight_pi_of_cell_count
    (V E F : ℕ)
    (hGB : (∫ x, D.scalarCurvature x ∂g.volumeMeasure) =
      4 * Real.pi * ((V : ℤ) - E + F))
    (hχ : (V : ℤ) - E + F ≤ 2) :
    (∫ x, D.scalarCurvature x ∂g.volumeMeasure) ≤ 8 * Real.pi := by
  have hGB' : (∫ x, D.scalarCurvature x ∂g.volumeMeasure) =
      4 * Real.pi * (((V : ℤ) - E + F : ℤ) : ℝ) := by
    simpa only [Int.cast_sub, Int.cast_add, Int.cast_natCast] using hGB
  exact D.integral_scalarCurvature_le_eight_pi_of_gaussBonnet
    ((V : ℤ) - E + F) hGB' hχ

theorem integral_scalarCurvature_le_eight_pi_of_incidence
    {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
    [Nonempty V] [Nonempty F]
    (ends : E → V × V) (adjacentFaces : E → F × F)
    (hV : PoincareConjecture.Surface.Combinatorial.Incidence.EndpointConnected ends)
    (hF : PoincareConjecture.Surface.Combinatorial.Incidence.EndpointConnected adjacentFaces)
    (hboundary :
      (PoincareConjecture.Surface.Combinatorial.Incidence.incidenceMatrix ends).transpose *
        PoincareConjecture.Surface.Combinatorial.Incidence.incidenceMatrix adjacentFaces = 0)
    (hGB : (∫ x, D.scalarCurvature x ∂g.volumeMeasure) =
      4 * Real.pi *
        ((Fintype.card V : ℤ) - Fintype.card E + Fintype.card F)) :
    (∫ x, D.scalarCurvature x ∂g.volumeMeasure) ≤ 8 * Real.pi := by
  have hχ := PoincareConjecture.Surface.Combinatorial.Incidence.eulerCount_le_two
    ends adjacentFaces hV hF hboundary
  have hGB' : (∫ x, D.scalarCurvature x ∂g.volumeMeasure) =
      4 * Real.pi *
        ((((Fintype.card V : ℤ) - Fintype.card E + Fintype.card F) : ℤ) : ℝ) := by
    simpa only [Int.cast_sub, Int.cast_add, Int.cast_natCast] using hGB
  exact D.integral_scalarCurvature_le_eight_pi_of_gaussBonnet
    ((Fintype.card V : ℤ) - Fintype.card E + Fintype.card F) hGB' hχ

theorem edge_slot_sum_eq_zero_of_pairing
    {F E : Type*} [Fintype F] [Fintype E]
    (edgeTerm : F → Fin 3 → ℝ)
    (slots : (F × Fin 3) ≃ (E × Fin 2))
    (hpair : ∀ e,
      edgeTerm (slots.symm (e, 0)).1 (slots.symm (e, 0)).2 +
          edgeTerm (slots.symm (e, 1)).1 (slots.symm (e, 1)).2 = 0) :
    (∑ f, ∑ i : Fin 3, edgeTerm f i) = 0 := by
  have hprod :
      (∑ p : F × Fin 3, edgeTerm p.1 p.2) =
        ∑ q : E × Fin 2, edgeTerm (slots.symm q).1 (slots.symm q).2 := by
    rw [← slots.symm.sum_comp]
  have hpair_sum :
      (∑ q : E × Fin 2, edgeTerm (slots.symm q).1 (slots.symm q).2) = 0 := by
    change Finset.sum ((Finset.univ : Finset E) ×ˢ (Finset.univ : Finset (Fin 2)))
      (fun q => edgeTerm (slots.symm q).1 (slots.symm q).2) = 0
    rw [Finset.sum_product]
    simp only [Fin.sum_univ_two]
    exact Finset.sum_eq_zero (fun e _ => hpair e)
  have hFprod :
      (∑ f, ∑ i : Fin 3, edgeTerm f i) =
        ∑ p : F × Fin 3, edgeTerm p.1 p.2 := by
    simpa using (Finset.sum_product (Finset.univ : Finset F)
      (Finset.univ : Finset (Fin 3)) (fun p => edgeTerm p.1 p.2)).symm
  rw [hFprod, hprod, hpair_sum]

def edgeVertexDegree
    {E V : Type*} [Fintype E] [DecidableEq V]
    (edgeVertex : E → Fin 2 → V) (v : V) : ℕ :=
  (Finset.univ.filter (fun q : E × Fin 2 => edgeVertex q.1 q.2 = v)).card

theorem sum_edgeVertexDegree_eq_two_card
    {E V : Type*} [Fintype E] [Fintype V] [DecidableEq V]
    (edgeVertex : E → Fin 2 → V) :
    (∑ v, edgeVertexDegree edgeVertex v) = 2 * Fintype.card E := by
  classical
  have hfiber := Finset.sum_fiberwise (Finset.univ : Finset (E × Fin 2))
    (fun q : E × Fin 2 => edgeVertex q.1 q.2) (fun _ => (1 : ℕ))
  have hcard :
      (∑ v, edgeVertexDegree edgeVertex v) = Fintype.card (E × Fin 2) := by
    change (∑ v, (Finset.univ.filter (fun q : E × Fin 2 =>
      edgeVertex q.1 q.2 = v)).card) = _
    simp_rw [Finset.card_eq_sum_ones]
    simpa using hfiber
  rw [hcard, Fintype.card_prod, Fintype.card_fin]
  ring

theorem corner_sum_eq_two_pi_card_sub_of_vertex_fans
    {F E V : Type*} [Fintype F] [Fintype E] [Fintype V] [DecidableEq V]
    (cornerTerm : F → Fin 3 → ℝ)
    (cornerVertex : F → Fin 3 → V)
    (degree : V → ℕ)
    (hfan : ∀ v,
      Finset.sum (Finset.univ.filter (fun p : F × Fin 3 =>
        cornerVertex p.1 p.2 = v)) (fun p => cornerTerm p.1 p.2) =
        Real.pi * (degree v : ℝ) - 2 * Real.pi)
    (hdegree : (∑ v, degree v) = 2 * Fintype.card E) :
      (∑ f, ∑ i : Fin 3, cornerTerm f i) =
      2 * Real.pi * ((Fintype.card E : ℝ) - Fintype.card V) := by
  classical
  let fan : V → ℝ := fun v =>
    Finset.sum (Finset.univ.filter (fun p : F × Fin 3 =>
      cornerVertex p.1 p.2 = v)) (fun p => cornerTerm p.1 p.2)
  have hpartition :
      (∑ p : F × Fin 3, cornerTerm p.1 p.2) = ∑ v, fan v := by
    have hfiber := Finset.sum_fiberwise (Finset.univ : Finset (F × Fin 3))
      (fun p : F × Fin 3 => cornerVertex p.1 p.2)
      (fun p : F × Fin 3 => cornerTerm p.1 p.2)
    simpa [fan] using hfiber.symm
  have hFprod :
      (∑ f, ∑ i : Fin 3, cornerTerm f i) =
        ∑ p : F × Fin 3, cornerTerm p.1 p.2 := by
    simpa using (Finset.sum_product (Finset.univ : Finset F)
      (Finset.univ : Finset (Fin 3)) (fun p => cornerTerm p.1 p.2)).symm
  rw [hFprod, hpartition]
  have hfan_sum :
      (∑ v, fan v) = ∑ v, (Real.pi * (degree v : ℝ) - 2 * Real.pi) := by
    apply Finset.sum_congr rfl
    intro v hv
    simpa [fan] using hfan v
  rw [hfan_sum]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hdegree' : (∑ v, (degree v : ℝ)) = 2 * Fintype.card E := by
    rw [← Nat.cast_sum, hdegree]
    norm_num
  rw [hdegree']
  ring

theorem sum_face_integrals_eq_four_pi_euler
    {F E V : Type*} [Fintype F] [Fintype E] [Fintype V]
    (faceIntegral : F → ℝ)
    (edgeTerm cornerTerm : F → Fin 3 → ℝ)
    (hlocal : ∀ f,
      faceIntegral f + 2 *
        ((∑ i : Fin 3, edgeTerm f i) + ∑ i : Fin 3, cornerTerm f i) =
        4 * Real.pi)
    (hedge : (∑ f, ∑ i : Fin 3, edgeTerm f i) = 0)
    (hvertex : (∑ f, ∑ i : Fin 3, cornerTerm f i) =
      2 * Real.pi * ((Fintype.card E : ℝ) - Fintype.card V)) :
    (∑ f, faceIntegral f) =
      4 * Real.pi *
        ((Fintype.card V : ℝ) - Fintype.card E + Fintype.card F) := by
  have hsum :
      (∑ f : F, (faceIntegral f + 2 *
        ((∑ i : Fin 3, edgeTerm f i) + ∑ i : Fin 3, cornerTerm f i))) =
        ∑ f : F, (4 * Real.pi) :=
    Finset.sum_congr rfl (fun f _ => hlocal f)
  have hlocal_sum :
      (∑ f : F, faceIntegral f) +
          2 * ((∑ f : F, ∑ i : Fin 3, edgeTerm f i) +
            ∑ f : F, ∑ i : Fin 3, cornerTerm f i) =
        ∑ f : F, (4 * Real.pi) := by
    calc
      _ = (∑ f : F, faceIntegral f) +
          ∑ f : F, 2 * ((∑ i : Fin 3, edgeTerm f i) +
            ∑ i : Fin 3, cornerTerm f i) := by
        congr 1
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ = ∑ f : F, (faceIntegral f + 2 *
          ((∑ i : Fin 3, edgeTerm f i) + ∑ i : Fin 3, cornerTerm f i)) := by
        rw [Finset.sum_add_distrib]
      _ = ∑ f : F, (4 * Real.pi) := hsum
  rw [hedge, hvertex] at hlocal_sum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hlocal_sum
  nlinarith

theorem integral_scalarCurvature_eq_four_pi_euler_of_face_assembly
    [CompactSpace S]
    (T : PoincareConjecture.Topology.Surface.FiniteSmoothTriangulation (M := S)) :
    letI := T.faces_finite
    letI := T.edges_finite
    letI := T.vertices_finite
    ∀ (edgeTerm cornerTerm : T.faces → Fin 3 → ℝ),
      (∀ f,
        (∫ x in (T.face f).carrier, D.scalarCurvature x ∂g.volumeMeasure) +
          2 *
            ((∑ i : Fin 3, edgeTerm f i) + ∑ i : Fin 3, cornerTerm f i) =
          4 * Real.pi) →
      (∑ f, ∑ i : Fin 3, edgeTerm f i) = 0 →
      (∑ f, ∑ i : Fin 3, cornerTerm f i) =
        2 * Real.pi *
          ((Fintype.card T.edges : ℝ) - Fintype.card T.vertices) →
      (∫ x, D.scalarCurvature x ∂g.volumeMeasure) =
        4 * Real.pi *
          ((Fintype.card T.vertices : ℝ) - Fintype.card T.edges +
            Fintype.card T.faces) := by
  let _ := T.faces_finite
  let _ := T.edges_finite
  let _ := T.vertices_finite
  intro edgeTerm cornerTerm hlocal hedge hvertex
  rw [T.integral_scalarCurvature_eq_sum_faces g D]
  exact sum_face_integrals_eq_four_pi_euler
    (fun f => ∫ x in (T.face f).carrier,
      D.scalarCurvature x ∂g.volumeMeasure) edgeTerm cornerTerm hlocal hedge hvertex

end PoincareConjecture.LeviCivitaData
