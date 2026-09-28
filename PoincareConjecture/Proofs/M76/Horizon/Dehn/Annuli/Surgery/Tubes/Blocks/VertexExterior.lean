import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.LocalVertexExterior
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.Blocks.IncidentQuarter



set_option autoImplicit false
open Set Metric Geometry Topology Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

open Classical in
theorem ComponentBranchModel.exists_local_vertex_exterior_point
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {S : Set E}
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X}
    {old : SourceCircleDecomposition f S} {i : old.Index}
    (D : ComponentBranchModel (e := e) (R := R) old i) [Fintype D.complex.faces]
    (hcore : D.core ⊆ interior R)
    (v : D.sample → ℝ × V3) (hv : v ∈ D.axis.vertices)
    {x y : E} (C : RawSourceCrossing e f S R x y)
    (hC : MapsTo (fun z ↦ (D.inverse z : X)) (D.complex.closedStar v).space C.chart.source)
    (hface : (D.complex.closedStar v).AffineOnFaces (fun z ↦ C.chart (D.inverse z)))
    (haxis : ∀ z ∈ (D.complex.closedStar v).space,
      z ∈ D.axis.space ↔ (D.inverse z : X) ∈ R ∧
        C.chart (D.inverse z) 0 = 0 ∧ C.chart (D.inverse z) 1 = 0)
    (hsheet : ∀ j : Fin 2,
      ((D.complex.closedStar v).vertexSubcomplex
        {z | (D.inverse z : X) ∈ R ∧ C.chart (D.inverse z) j.castSucc = 0}).space =
      (D.complex.closedStar v).space ∩
        {z | (D.inverse z : X) ∈ R ∧ C.chart (D.inverse z) j.castSucc = 0})
    (s : Bool → Finset (D.sample → ℝ × V3)) (hs : ∀ j, s j ∈ D.axis.faces)
    (hcard : ∀ j, (s j).card = 2) (hvs : ∀ j, v ∈ s j)
    (hdisj : Disjoint (D.complex.barycentricDualBlock (s false)).space
      (D.complex.barycentricDualBlock (s true)).space) (signs : Fin 2 → Bool) :
    ∃ z ∈ (D.complex.barycentricDualBlock {v}).space,
      z ∈ ((D.complex.barycentricDualBlock {v}).link v).space ∧
      (∀ j, z ∉ (D.complex.barycentricDualBlock (s j)).space) ∧
      ∀ j : Fin 2, if signs j then 0 < C.chart (D.inverse z) j.castSucc
        else C.chart (D.inverse z) j.castSucc < 0 := by
  classical
  let V := D.complex.barycentricDualBlock {v}
  let J := fun j => (D.complex.barycentricDualBlock (s j)).space
  have hmodel := exists_original_vertex_coordinate_model D.complex D.homeomorph D.inverse
    D.inverse_value v (D.axis_le hv) (D.vertex_mem_interior_core v hv) C.chart
    (by convert hC using 1; congr 3; exact Subsingleton.elim _ _)
    (by convert hface using 1; congr 2; exact Subsingleton.elim _ _)
  obtain ⟨C0, L, theta, hcompact, hconvex, hzero, _, _, _, _, hlink, hmarks⟩ := hmodel
  have hlink' (z : V.space) : (z : D.sample → ℝ × V3) ∈ (V.link v).space ↔
      (theta z : V3) ∈ frontier C0 := by
    convert hlink z using 1
    apply Iff.of_eq
    congr 4
    exact Subsingleton.elim _ _
  have hvstar : v ∈ (D.complex.closedStar v).space := by
    apply (D.complex.closedStar v).vertices_subset_space
    exact ⟨D.axis_le hv, by simpa using (show {v} ∈ D.complex.faces from D.axis_le hv)⟩
  have hvzero := (haxis v hvstar).mp (D.axis.vertices_subset_space hv)
  have hmarks' (j : Fin 2) (z : V.space) :
      ((theta z : V3) j.castSucc = 0 ↔ C.chart (D.inverse z) j.castSucc = 0) ∧
      (0 ≤ (theta z : V3) j.castSucc ↔ 0 ≤ C.chart (D.inverse z) j.castSucc) := by
    have hj : C.chart (D.inverse v) j.castSucc = 0 := by
      fin_cases j
      · exact hvzero.2.1
      · exact hvzero.2.2
    simpa only [Pi.sub_apply, hj, sub_zero] using hmarks j.castSucc z
  have hJV (j : Bool) : J j ⊆ V.space :=
    space_subset_of_le (D.complex.barycentricDualBlock_antitone
      (Finset.singleton_subset_iff.mpr (hvs j)))
  have hJ (j : Bool) : IsCompact (J j) :=
    (D.complex.barycentricDualBlock (s j)).isCompact_space_of_finite
      (D.complex.barycentricDualBlock_finite (s j))
  have hmeet (b : Bool) : ∃ z : V.space, (z : D.sample → ℝ × V3) ∈ J b ∧
      (theta z : V3) ∈ frontier C0 ∧ (theta z : V3) ∈ strictCoordinateWedge signs := by
    obtain ⟨a, b', hab, hQ, _, _, _, _, hQlink⟩ := D.local_incident_quarter hcore (s b)
      (hs b) (hcard b) v (hvs b) C hC hface haxis hsheet signs
    obtain ⟨z, hzQ, hzboundary⟩ := hQ.sdiff_nonempty
    have hstrict (j : Fin 2) : if signs j then 0 < C.chart (D.inverse z) j.castSucc
        else C.chart (D.inverse z) j.castSucc < 0 := by
      have hne : C.chart (D.inverse z) j.castSucc ≠ 0 := by
        intro he
        apply hzboundary
        right
        fin_cases j
        · exact Or.inl ⟨hzQ, he⟩
        · exact Or.inr ⟨hzQ, he⟩
      have hw := hzQ.2 j
      cases hj : signs j <;> simp only [SignedJointCross.side, hj, Bool.false_eq_true,
        if_false, if_true] at hw ⊢
      · exact lt_of_le_of_ne hw hne
      · exact lt_of_le_of_ne hw (Ne.symm hne)
    let zv : V.space := ⟨z, hJV b hzQ.1⟩
    refine ⟨zv, hzQ.1, (hlink' zv).mp (hQlink hzQ), ?_⟩
    intro j
    have hj := hstrict j
    cases he : signs j <;> simp only [he, Bool.false_eq_true, if_false, if_true] at hj ⊢
    · exact lt_of_not_ge (fun h => not_le_of_gt hj ((hmarks' j zv).2.mp h))
    · refine lt_of_le_of_ne ((hmarks' j zv).2.mpr hj.le) ?_
      intro heq
      exact hj.ne' ((hmarks' j zv).1.mp heq.symm)
  obtain ⟨z, hzfront, hzstrict, hzJ⟩ :=
    exists_strict_chart_frontier_point_outside_two_compact_sets theta hcompact hconvex hzero
      J hJ hJV hdisj signs hmeet
  refine ⟨z, z.property, (hlink' z).mpr hzfront, hzJ, ?_⟩
  intro j
  have hj := hzstrict j
  cases he : signs j <;> simp only [he, Bool.false_eq_true, if_false, if_true] at hj ⊢
  · exact lt_of_not_ge (fun h => not_le_of_gt hj ((hmarks' j z).2.mpr h))
  · refine lt_of_le_of_ne ((hmarks' j z).2.mp hj.le) ?_
    intro heq
    exact hj.ne' ((hmarks' j z).1.mpr heq.symm)

end PoincareConjecture.M76.Dehn.Annuli
