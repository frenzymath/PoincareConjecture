import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Intervals.ModelArc
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.OriginalDoubleArcTubeMap










set_option autoImplicit false
open Set Metric Geometry Topology unitInterval

namespace PoincareConjecture.M76.Dehn
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1
local notation "I01" => Icc (0 : ℝ) 1



theorem OrdinaryDoubleCurveModel.exists_interval_tube_model
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
    (old : OrdinaryDoubleCurveModel e f R) (hf : PolyhedralPLInCharts e f D2)
    (he : PLDomain e R) (i : old.Index)
    (hball : IsFinitePLBallPair ℝ (old.pieces i) (old.pieces i ∩ Q2))
    (hin : MapsTo f D2 R) (hfront : ∀ x ∈ D2, f x ∈ frontier R ↔ x ∈ Q2) :
    ∃ D : OrdinaryIntervalMarkedModel old i,
      letI : ∀ j, Fintype (D.marks j).faces := fun j ↦ (D.marks_full j).2.1.fintype
      ∃ (a : I01 ≃ₜ old.pieces i)
      (b : I01 ≃ₜ (D.marks (.inr 2)).space)
      (tube : ↥(signedTubeDiamond ×ˢ I01) ≃ₜ
        ((D.marks (.inl false)).barycentricNeighborhood (D.marks (.inr 2))).space),
      a.IsFinitePL ∧ b.IsFinitePL ∧ tube.IsFinitePL ∧
      (∀ t : I01, (b t : D.sample → ℝ × V3) = D.graph (f (a t))) ∧
      (∀ t : I01, (D.inverse (b t) : X) = f (a t)) ∧
      (∀ t : I01, (tube ⟨((0, 0), t), signedTubeRadius_subset_diamond 0 false
        (left_mem_segment ℝ _ _), t.property⟩ : D.sample → ℝ × V3) = b t) ∧
      (∀ j (x : ↥(signedTubeDiamond ×ˢ I01)),
        (x : (ℝ × ℝ) × ℝ).1 ∈ signedTubeSheet j ↔
          (tube x : D.sample → ℝ × V3) ∈ (D.marks (.inr j.castSucc)).space) ∧
      ∀ x : ↥(signedTubeDiamond ×ˢ I01),
        (tube x : D.sample → ℝ × V3) ∈ (D.marks (.inl true)).space ↔
          (x : (ℝ × ℝ) × ℝ).2 = 0 ∨ (x : (ℝ × ℝ) × ℝ).2 = 1 := by
  classical
  obtain ⟨D⟩ := old.nonempty_interval_marked_model hf he i hball hin hfront
  obtain ⟨a, b, ha, hb, hbval, hgb, hcontact⟩ := D.exists_arc_parameters hf hin hfront hball
  let _ : Fintype D.complex.faces := D.complex_finite.fintype
  let _ (j) : Fintype (D.marks j).faces := (D.marks_full j).2.1.fintype
  have hAR : f '' old.pieces i ⊆ R := by
    rintro _ ⟨x, hx, rfl⟩
    exact hin (old.piece_subset_double i hx).1
  have hAF : ((f '' old.pieces i) ∩ frontier R).Finite := by
    obtain ⟨p, q, _, hpq⟩ := hball.exists_boundary_eq_pair
    have hfin : (old.pieces i ∩ Q2).Finite := hpq.symm ▸ (Set.toFinite {p, q})
    apply (hfin.image f).subset
    rintro y ⟨⟨x, hx, rfl⟩, hxf⟩
    exact ⟨x, ⟨hx, (hfront x (old.piece_subset_double i hx).1).mp hxf⟩, rfl⟩
  have harc (z : D.sample → ℝ × V3) (hz : z ∈ D.complex.space) :
      z ∈ (D.marks (.inr 2)).space ↔ (D.inverse z : X) ∈ f '' old.pieces i := by
    have h := D.mem_mark_image (D.marks_image 2) z hz
    simpa only [D.selected_source] using h
  choose point hmap hface using fun p : (D.marks (.inr 2)).vertices ↦
    D.selected_stars p p.property
  let B (p : (D.marks (.inr 2)).vertices) := D.charts (point p)
  have hB (p : (D.marks (.inr 2)).vertices) :
      MapsTo (fun z ↦ (D.inverse z : X)) (D.complex.closedStar p).space (B p).source ∧
      (D.complex.closedStar p).AffineOnFaces (fun z ↦ B p (D.inverse z)) ∧
      (∀ y ∈ (B p).source, y ∈ f '' old.pieces i ↔
        y ∈ R ∧ B p y 0 = 0 ∧ B p y 1 = 0) ∧
      ∀ j : Fin 2, ∀ y ∈ (B p).source,
        y ∈ f '' (D.source j.castSucc).space ↔ y ∈ R ∧ B p y j.castSucc = 0 := by
    refine ⟨hmap p, hface p, D.chart_axis (point p), ?_⟩
    intro j y hy
    fin_cases j
    · exact (D.chart_left (point p) y hy).trans and_comm
    · exact (D.chart_right (point p) y hy).trans and_comm
  obtain ⟨tube, htube, haxis, hsheet, hends⟩ := exists_original_signed_tube_map
    D.core_neighborhood hAR hAF (fun j : Fin 2 ↦ f '' (D.source j.castSucc).space)
    D.complex D.graph D.graph_continuous D.homeomorph D.homeomorph_value
    D.inverse D.inverse_value D.inverse_PL D.marks
    (fun j ↦ (D.marks_full j).1) (fun j ↦ (D.marks_full j).2.2)
    (.inl false) (.inl true) (.inr 2) (fun j : Fin 2 ↦ .inr j.castSucc)
    (D.mem_mark_image D.region_image) (D.mem_mark_image D.frontier_image) harc
    (fun j ↦ D.mem_mark_image (D.marks_image j.castSucc)) B (by
      convert hB using 1
      have hdec : (fun a b : D.sample → ℝ × V3 ↦ Fintype.decidablePiFintype a b) =
          Classical.decEq _ := Subsingleton.elim _ _
      rw [hdec])
    (fun p ↦ D.chart_region (point p)) b hb hcontact
  exact ⟨D, a, b, tube, ha, hb, htube, hbval, hgb, haxis, hsheet, hends⟩

end PoincareConjecture.M76.Dehn
