import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CoveredReturnBands
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ReturnBandLines
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.PolygonalCores
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Area.Triangulation










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold Matrix
open PoincareConjecture.Topology.Surface Poincare.Topology.Plane.Meshes

namespace PoincareConjecture

private theorem finite_faces_frontier_null {I : Type*} [Finite I]
    (face : I → SmoothFace AnnulusCoordinates) (g : RiemannianMetric 2 AnnulusCoordinates) :
    g.volumeMeasure (frontier (⋃ i, (face i).carrier)) = 0 := by
  apply measure_mono_null
    (Poincare.Topology.frontier_iUnion_subset_iUnion_frontier_of_isClosed
      (fun i => (face i).carrier) (fun i => (face i).isClosed_carrier))
  exact measure_iUnion_null (fun i => (face i).volumeMeasure_frontier_eq_zero g)

private theorem interiors_disjoint_of_inter_frontier {A B : Set AnnulusCoordinates}
    (h : A ∩ B ⊆ frontier B) : Disjoint (interior A) (interior B) := by
  apply disjoint_left.mpr
  intro z hzA hzB
  exact disjoint_left.mp disjoint_interior_frontier hzB
    (h ⟨interior_subset hzA, interior_subset hzB⟩)

open Classical in





theorem m64Intrinsic_exists_retained_return_core
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T : ℝ} (hT : 0 < T)
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hregular : ∀ t ∈ Ioo (0 : ℝ) T, deriv gamma t ≠ 0)
    (hind : LinearIndependent ℝ
      (![deriv gamma 0, -deriv gamma T] : Fin 2 → AnnulusCoordinates))
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T) (hcompact : IsCompact (closure U))
    (hray : ∀ t ∈ Ioo (0 : ℝ) T, ∀ᶠ z in 𝓝[>] (0 : ℝ),
      gamma t + z • Poincare.Topology.Plane.Curves.quarterTurn (deriv gamma t) ∈ U) :
    ∃ (n : ℕ) (pieces : Option (Fin n) → Set AnnulusCoordinates)
      (lines : List (AnnulusCoordinates →ᵃ[ℝ] ℝ)) (mesh : TriangleMesh),
      0 < n ∧
      (∀ i, IsCompact (pieces i) ∧ closure (interior (pieces i)) = pieces i) ∧
      (∀ i, pieces i ⊆ closure U) ∧
      Pairwise (fun i j => Disjoint (interior (pieces i)) (interior (pieces j))) ∧
      (∀ (g : RiemannianMetric 2 AnnulusCoordinates) i,
        g.volumeMeasure (frontier (pieces i)) = 0) ∧
      (∀ i, frontier (pieces i) ⊆ gamma '' Icc 0 T ∪ ⋃ l ∈ lines, {z | l z = 0}) ∧
      (∀ l ∈ lines, Function.Surjective l) ∧
      mesh.toPlaneComplex.support = closure (U \ ⋃ i, pieces i) ∧
      mesh.toPlaneComplex.support ⊆ U ∧
      closure U = (⋃ i, pieces i) ∪ mesh.toPlaneComplex.support ∧
      (∀ i, mesh.toPlaneComplex.support ∩ pieces i ⊆
        frontier (pieces i) ∩ ⋃ l ∈ lines, {z | l z = 0}) ∧
      (∀ (g : RiemannianMetric 2 AnnulusCoordinates) (q : AnnulusCoordinates → ℝ),
        Continuous q →
        (∫ x in closure U, q x ∂g.volumeMeasure) =
          (∑ i, ∫ x in pieces i, q x ∂g.volumeMeasure) +
            ∫ x in mesh.toPlaneComplex.support, q x ∂g.volumeMeasure) ∧
      ∃ (b : AffineBasis (Fin 3) ℝ Plane)
        (refinementLines : List (Plane →ᵃ[ℝ] ℝ))
        (P : Finset ((TriangleMesh.single b b.ind).refineByLines refinementLines).Vertex → Prop),
        mesh = ((TriangleMesh.single b b.ind).refineByLines refinementLines).restrictTriangles P ∧
        mesh.toPlaneComplex.support ⊆ interior (convexHull ℝ (range b)) := by
  classical
  obtain ⟨H, r, F, positive, d, hr, hrbound, _, _, _, _, haxis, haxis', _, hF,
    hCcompact, hCsub, _, n, c, L, G, f, ell, hn, hc, hfirst, hlast, _,
    B, hB, hsep, hadj, hcapB, hcover⟩ :=
    m64Intrinsic_exists_covered_return_bands hg hT hend hinj hregular hind
      hU hV hdisj hfU hfV hray
  let occupied (i : Bool × Bool) := if positive then i = (true, true) else i ≠ (true, true)
  let caps (i : Bool × Bool) :=
    F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r}
  let C := ⋃ i, ⋃ (_ : occupied i), caps i
  let pieces : Option (Fin n) → Set AnnulusCoordinates
    | none => C
    | some i => (B i).carrier
  have hpieces : (⋃ i, pieces i) = C ∪ ⋃ i, (B i).carrier := by
    ext z
    constructor
    · intro hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      cases i with
      | none => exact Or.inl hi
      | some i => exact Or.inr (mem_iUnion.mpr ⟨i, hi⟩)
    · rintro (hz | hz)
      · exact mem_iUnion.mpr ⟨none, hz⟩
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hz
        exact mem_iUnion.mpr ⟨some i, hi⟩
  have hcaplines := m64Intrinsic_retained_caps_frontier_lines hr (by linarith : r ≤ T)
    H F positive haxis haxis' (fun i => (hF i).1) (fun i => (hF i).2.2.1)
      (fun i => (hF i).2.2.2.1) (fun i => (hF i).2.2.2.2.1)
      (fun i => (hF i).2.2.2.2.2.1) (fun i => (hF i).2.2.2.2.2.2.1)
      (fun i => (hF i).2.2.2.2.2.2.2.1)
  obtain ⟨_, hCregular, caplines, hcaplines, hcapfront⟩ := hcaplines
  have hclosed (i : Option (Fin n)) : IsCompact (pieces i) ∧
      closure (interior (pieces i)) = pieces i := by
    cases i with
    | none => exact ⟨hCcompact, hCregular⟩
    | some i =>
      exact ⟨isCompact_iUnion (fun j => ((B i).face j).isCompact_carrier),
        (B i).closure_interior_carrier⟩
  have hsub (i : Option (Fin n)) : pieces i ⊆ closure U := by
    cases i with
    | none => exact hCsub
    | some i => exact (hB i).2.2.2.1
  have hcapint (i : Fin n) : C ∩ (B i).carrier ⊆ frontier (B i).carrier := by
    rw [hcapB i]
    intro z hz
    apply (B i).outer_boundaries_subset_frontier
    rcases hz with hz | hz
    · left
      right
      split_ifs at hz with h
      · exact hz
      · exact False.elim (notMem_empty z hz)
    · right
      split_ifs at hz with h
      · exact hz
      · exact False.elim (notMem_empty z hz)
  have hbandint (i j : Fin n) (hij : i < j) :
      Disjoint (interior (B i).carrier) (interior (B j).carrier) := by
    by_cases hnext : i.succ = j.castSucc
    · apply interiors_disjoint_of_inter_frontier
      rw [hadj i j hnext, hnext, ← (hB j).2.1]
      exact fun _ hz => (B j).outer_boundaries_subset_frontier (Or.inl (Or.inr hz))
    · have hgap : i.succ < j.castSucc := by
        apply Fin.mk_lt_mk.mpr
        have hne : i.val + 1 ≠ j.val := fun h => hnext (Fin.ext h)
        have hlt : i.val < j.val := hij
        omega
      exact (hsep i j hgap).mono interior_subset interior_subset
  have hdisjoint : Pairwise (fun i j =>
      Disjoint (interior (pieces i)) (interior (pieces j))) := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some j => exact interiors_disjoint_of_inter_frontier (hcapint j)
    | some i =>
      cases j with
      | none => exact (interiors_disjoint_of_inter_frontier (hcapint i)).symm
      | some j =>
        have hne : i ≠ j := fun h => hij (congrArg some h)
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact hbandint i j hlt
        · exact (hbandint j i hgt).symm
  have hnull (g : RiemannianMetric 2 AnnulusCoordinates) (i : Option (Fin n)) :
      g.volumeMeasure (frontier (pieces i)) = 0 := by
    cases i with
    | none =>
      choose face _ _ hcarrier _ using fun j =>
        m64Intrinsic_exists_face_of_chosen_cap (F j) hr (hF j).1
          (hF j).2.2.1 (hF j).2.2.2.1
      have heq : C = ⋃ j : {j : Bool × Bool // occupied j}, (face j).carrier := by
        ext z
        simp only [C, caps, mem_iUnion, Subtype.exists, hcarrier]
      change g.volumeMeasure (frontier C) = 0
      rw [heq]
      exact finite_faces_frontier_null _ g
    | some i => exact finite_faces_frontier_null (B i).face g
  have hcut (k : Fin (n + 1)) : c k ∈ Icc r (T - r) := by
    exact ⟨by simpa only [hfirst] using hc.monotone (Fin.zero_le k),
      by simpa only [hlast] using hc.monotone (Fin.le_last k)⟩
  have hlocallines (i : Option (Fin n)) :
      ∃ lines : List (AnnulusCoordinates →ᵃ[ℝ] ℝ),
        (∀ l ∈ lines, Function.Surjective l) ∧
        frontier (pieces i) \ gamma '' Icc 0 T ⊆ ⋃ l ∈ lines, {z | l z = 0} := by
    cases i with
    | none => exact ⟨caplines, hcaplines, fun z hz => (hcapfront hz.1).resolve_left hz.2⟩
    | some i =>
      obtain ⟨lines, hlines, hfront⟩ := m64Intrinsic_linear_band_frontier_lines (L i).symm (B i)
      refine ⟨lines, hlines, ?_⟩
      intro z hz
      apply (hfront hz.1).resolve_left
      intro hlower
      apply hz.2
      rw [(hB i).1] at hlower
      exact image_mono (Icc_subset_Icc (hr.le.trans (hcut i.castSucc).1)
        ((hcut i.succ).2.trans (sub_le_self T hr.le))) hlower
  obtain ⟨lines, hlines, hlinesub⟩ := Poincare.Topology.Plane.exists_affine_lines_iUnion
    (fun i => frontier (pieces i) \ gamma '' Icc 0 T) hlocallines
  have hfront (i : Option (Fin n)) : frontier (pieces i) ⊆
      gamma '' Icc 0 T ∪ ⋃ l ∈ lines, {z | l z = 0} := by
    intro z hz
    by_cases htrace : z ∈ gamma '' Icc 0 T
    · exact Or.inl htrace
    · exact Or.inr (hlinesub (mem_iUnion.mpr ⟨i, hz, htrace⟩))
  have hsource : closure U ⊆ (chartAt AnnulusCoordinates (0 : AnnulusCoordinates)).source := by
    intro z _
    simp
  have hfront' (i : Option (Fin n)) : frontier (pieces i) ⊆ gamma '' Icc 0 T ∪
      (chartAt AnnulusCoordinates (0 : AnnulusCoordinates)) ⁻¹'
        (⋃ l ∈ lines, {z | l z = 0}) := by
    simpa using hfront i
  obtain ⟨mesh, hsupport, _, _, hinside, hrecovery, hinter, hrefinement⟩ :=
    exists_exact_polygonal_remainder_mesh_with_refinement (0 : AnnulusCoordinates)
      hU hcompact hsource pieces (fun i => (hclosed i).1.isClosed) hsub
      (subset_of_eq hfU) lines hlines hfront' (by
        intro z hz
        obtain ⟨p, hp, rfl⟩ := hz.2
        obtain ⟨W, hW, hpW, hcoverW⟩ := hcover p hp
        exact ⟨W, hW, hpW, hpieces.symm ▸ hcoverW⟩)
  have hmeshRecovery : closure U = (⋃ i, pieces i) ∪ mesh.toPlaneComplex.support := by
    simpa using hrecovery
  have hmeshContact (i : Option (Fin n)) : mesh.toPlaneComplex.support ∩ pieces i ⊆
      frontier (pieces i) ∩ ⋃ l ∈ lines, {z | l z = 0} := by
    simpa using hinter i
  have hintegral (g : RiemannianMetric 2 AnnulusCoordinates) (q : AnnulusCoordinates → ℝ)
      (hq : Continuous q) :
      (∫ x in closure U, q x ∂g.volumeMeasure) =
        (∑ i, ∫ x in pieces i, q x ∂g.volumeMeasure) +
          ∫ x in mesh.toPlaneComplex.support, q x ∂g.volumeMeasure := by
    have hpair : Pairwise (fun i j => AEDisjoint g.volumeMeasure (pieces i) (pieces j)) := by
      intro i j hij
      apply measure_mono_null _ (hnull g j)
      have hd := (hdisjoint hij).closure_left isOpen_interior
      rw [(hclosed i).2] at hd
      intro z hz
      exact ⟨subset_closure hz.2, fun hzint => disjoint_left.mp hd hz.1 hzint⟩
    have hcore : AEDisjoint g.volumeMeasure (⋃ i, pieces i) mesh.toPlaneComplex.support := by
      change g.volumeMeasure ((⋃ i, pieces i) ∩ mesh.toPlaneComplex.support) = 0
      rw [iUnion_inter]
      apply measure_iUnion_null
      intro i
      apply measure_mono_null _ (hnull g i)
      exact fun z hz => (hmeshContact i ⟨hz.2, hz.1⟩).1
    have hboundaryCompact := isCompact_iUnion (fun i => (hclosed i).1)
    have hbint := hq.continuousOn.integrableOn_compact hboundaryCompact (μ := g.volumeMeasure)
    have hmint := hq.continuousOn.integrableOn_compact mesh.toPlaneComplex.isCompact_support
      (μ := g.volumeMeasure)
    have hsum := integral_iUnion_ae
      (fun i => (hclosed i).1.measurableSet.nullMeasurableSet) hpair hbint
    rw [hmeshRecovery, setIntegral_union₀ hcore
      mesh.toPlaneComplex.isCompact_support.measurableSet.nullMeasurableSet hbint hmint]
    congr 1
    simpa only [tsum_fintype] using hsum
  refine ⟨n, pieces, lines, mesh, hn, hclosed, hsub, hdisjoint, hnull, hfront, hlines,
    ?_, ?_, hmeshRecovery, hmeshContact, hintegral, hrefinement⟩
  · simpa using hsupport
  · simpa using hinside

end PoincareConjecture
