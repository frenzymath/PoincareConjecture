import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Crossings.ComponentAxisCharts
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Crossings.SelectedChartStars
import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcTubeModel









set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1

theorem OrdinaryDoubleCurveModel.exists_component_axis_model_with_raw_branches
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
    (old : OrdinaryDoubleCurveModel e f R) (hf : PolyhedralPLInCharts e f D2)
    (he : PLDomain e R) (i : old.Index)
    (P : SimplicialComplex ℝ V2) (hP : P.faces.Finite) (hPs : P.space = old.pieces i)
    {W : Set X} (hW : IsOpen W) (hAW : f '' old.pieces i ⊆ W) :
    ∃ (s : Finset (f '' old.pieces i)) (F : X → (s → ℝ × V3)) (C : Set X)
      (K A : SimplicialComplex ℝ (s → ℝ × V3))
      (H : C ≃ₜ K.space) (g : (s → ℝ × V3) → C)
      (B : f '' old.pieces i → OpenPartialHomeomorph X V3),
      IsCompact C ∧ f '' old.pieces i ⊆ interior C ∧ C ⊆ W ∧ Continuous F ∧
      (∀ x ∈ C, ∀ y : X, F x = F y → x = y) ∧ K.faces.Finite ∧ A ≤ K ∧
      (∀ t ∈ K.faces, (∀ v ∈ t, v ∈ A.vertices) → t ∈ A.faces) ∧
      K.space = F '' C ∧ A.space = (F ∘ f) '' old.pieces i ∧
      (∀ x : C, (H x : s → ℝ × V3) = F x) ∧
      (∀ z : K.space, (g z : X) = (H.symm z : X)) ∧
      PolyhedralPLInCharts e (fun z ↦ (g z : X)) K.space ∧
      FinitePiecewiseAffineOn (F ∘ f) (old.pieces i) ∧
      (∀ y, (y : X) ∈ (B y).source ∧ (B y).source ⊆ W ∧
        (∀ k, (e k).symm.trans (B y) ∈ piecewiseAffineGroupoid V3) ∧
        ∀ z ∈ (B y).source,
          z ∈ f '' old.pieces i ↔ z ∈ R ∧ B y z 0 = 0 ∧ B y z 1 = 0) ∧
      (∀ p ∈ A.vertices, ∃ y : f '' old.pieces i,
        MapsTo (fun z ↦ (g z : X)) (K.closedStar p).space (B y).source ∧
        (K.closedStar p).AffineOnFaces (fun z ↦ B y (g z))) ∧
      (∀ z : f '' old.pieces i, ∃ (x y : V2) (D : RawCrossingChart e f R x y),
        f x = z ∧ (B z : X → V3) = D.chart ∧ (B z).source ⊆ D.chart.source) ∧
      ∃ (S : SimplicialComplex ℝ (s → ℝ × V3)) (T : SimplicialComplex ℝ V2),
        S ≤ K ∧ (∀ t ∈ K.faces, (∀ v ∈ t, v ∈ S.vertices) → t ∈ S.faces) ∧
        T.faces.Finite ∧ T.space = D2 ∩ f ⁻¹' C ∧
        FinitePiecewiseAffineOn (F ∘ f) T.space ∧
        S.space = (F ∘ f) '' T.space := by
  classical
  obtain ⟨O, B, hO, hAO, hOW, _, hB⟩ := old.exists_component_axis_charts hf i hW hAW
  have hPD : P.space ⊆ D2 := fun x hx ↦ (old.piece_subset_double i (hPs ▸ hx)).1
  have hAc : IsCompact (f '' old.pieces i) := (old.compact i).image_of_continuousOn
    (hf.continuousOn.mono (fun x hx ↦ (old.piece_subset_double i hx).1))
  have hAn : (f '' old.pieces i).Nonempty := (old.connected i).nonempty.image f
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨Q, hQ, hQs, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_unit_cube : IsFinitePLBallPair V2 D2 (sphere (0 : V2) 1))
  let sources (b : Bool) := if b then Q else P
  have hsourceFinite (b : Bool) : (sources b).faces.Finite := by
    cases b <;> assumption
  have hsourcePL (b : Bool) : PolyhedralPLInCharts e f (sources b).space := by
    cases b
    · exact hf.restrict_finite P hP hPD
    · exact hQs.symm ▸ hf
  obtain ⟨s, F, C, K0, J, H0, g, T, hC, hAC, hCO, hFc, _, hsep, hK0,
      hJ, hK0s, _, _, hJimage, hT, hH0, _, hg, hgPL, _⟩ :=
    exists_original_signed_tube_model he hAc hAn hO hAO (fun _ : Bool ↦ V2)
      sources hsourceFinite (fun _ ↦ f) hsourcePL
  have htrace : K0.space ∩ (fun z ↦ (g z : X)) ⁻¹' (f '' old.pieces i) =
      F '' (f '' old.pieces i) := by
    ext z
    constructor
    · rintro ⟨hz, hgz⟩
      refine ⟨g z, hgz, ?_⟩
      exact (congrArg F (hg ⟨z, hz⟩)).trans ((hH0 (H0.symm ⟨z, hz⟩)).symm.trans
        (congrArg Subtype.val (H0.apply_symm_apply ⟨z, hz⟩)))
    · rintro ⟨x, hx, rfl⟩
      have hxC : x ∈ C := interior_subset (hAC hx)
      have hxK : F x ∈ K0.space := hK0s.symm ▸ mem_image_of_mem F hxC
      refine ⟨hxK, ?_⟩
      have hv : (g (F x) : X) = x := by
        simpa only [hH0, H0.symm_apply_apply] using hg (H0 ⟨x, hxC⟩)
      change (g (F x) : X) ∈ f '' old.pieces i
      rw [hv]
      exact hx
  have hJa : (J (.inr false)).space =
      K0.space ∩ (fun z ↦ (g z : X)) ⁻¹' (f '' old.pieces i) := by
    rw [hJimage, htrace, show (sources false).space = P.space from rfl, hPs]
    congr 1
    exact inter_eq_right.mpr (fun x hx ↦ interior_subset (hAC hx))
  let G (q : (K0.space ∩ (fun z ↦ (g z : X)) ⁻¹' (f '' old.pieces i) : Set _)) :=
    B ⟨g q, q.property.2⟩
  have hJK (j : Sum Bool Bool) : (J j).space ⊆ K0.space :=
    SimplicialComplex.space_subset_of_le (hJ j).1
  obtain ⟨K, M, hK, hKK0, hM, hstars⟩ := exists_selected_compatible_chart_stars
    e he.compatible he.cover K0 hK0 hgPL hAc.isClosed G
      (fun q k ↦ (hB ⟨g q, q.property.2⟩).2.2.1 k)
      (fun q ↦ (hB ⟨g q, q.property.2⟩).1)
      J (fun j ↦ (hJ j).2.1) hJK (.inr false) hJa
  let H : C ≃ₜ K.space := H0.trans (Homeomorph.setCongr hKK0.space_eq.symm)
  have hTspace : (T false).space = old.pieces i := by
    rw [(hT false).2.1, show (sources false).space = P.space from rfl, hPs]
    apply inter_eq_left.mpr
    intro x hx
    change f x ∈ C
    exact interior_subset (hAC ⟨x, hx, rfl⟩)
  have hAs : (M (.inr false)).space = (F ∘ f) '' old.pieces i := by
    rw [(hM (.inr false)).2.1, hJa, htrace, image_comp]
  have hFf : FinitePiecewiseAffineOn (F ∘ f) (old.pieces i) := by
    simpa only [hTspace] using (hT false).2.2.1
  refine ⟨s, F, C, K, M (.inr false), H, g, B, hC, hAC, hCO.trans hOW, hFc, hsep,
    hK, (hM (.inr false)).1, (hM (.inr false)).2.2, hKK0.space_eq.trans hK0s,
    hAs, hH0, (fun z ↦ hg ⟨z, hKK0.space_eq.subset z.property⟩),
    hKK0.space_eq.symm ▸ hgPL, hFf, ?_, ?_, fun z => (hB z).2.2.2.2, ?_⟩
  · intro y
    exact ⟨(hB y).1, (hB y).2.1.trans hOW, (hB y).2.2.1, (hB y).2.2.2.1⟩
  · intro p hp
    obtain ⟨q, hq⟩ := hstars p hp
    exact ⟨⟨g q, q.property.2⟩, hq⟩
  · refine ⟨M (.inr true), T true, (hM (.inr true)).1, (hM (.inr true)).2.2,
      (hT true).1, ?_, (hT true).2.2.1, ?_⟩
    · simpa only [sources, if_true, hQs] using (hT true).2.1
    · exact (hM (.inr true)).2.1.trans (hT true).2.2.2.symm



theorem OrdinaryDoubleCurveModel.exists_component_axis_model
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
    (old : OrdinaryDoubleCurveModel e f R) (hf : PolyhedralPLInCharts e f D2)
    (he : PLDomain e R) (i : old.Index)
    (P : SimplicialComplex ℝ V2) (hP : P.faces.Finite) (hPs : P.space = old.pieces i)
    {W : Set X} (hW : IsOpen W) (hAW : f '' old.pieces i ⊆ W) :
    ∃ (s : Finset (f '' old.pieces i)) (F : X → (s → ℝ × V3)) (C : Set X)
      (K A : SimplicialComplex ℝ (s → ℝ × V3))
      (H : C ≃ₜ K.space) (g : (s → ℝ × V3) → C)
      (B : f '' old.pieces i → OpenPartialHomeomorph X V3),
      IsCompact C ∧ f '' old.pieces i ⊆ interior C ∧ C ⊆ W ∧ Continuous F ∧
      (∀ x ∈ C, ∀ y : X, F x = F y → x = y) ∧ K.faces.Finite ∧ A ≤ K ∧
      (∀ t ∈ K.faces, (∀ v ∈ t, v ∈ A.vertices) → t ∈ A.faces) ∧
      K.space = F '' C ∧ A.space = (F ∘ f) '' old.pieces i ∧
      (∀ x : C, (H x : s → ℝ × V3) = F x) ∧
      (∀ z : K.space, (g z : X) = (H.symm z : X)) ∧
      PolyhedralPLInCharts e (fun z ↦ (g z : X)) K.space ∧
      FinitePiecewiseAffineOn (F ∘ f) (old.pieces i) ∧
      (∀ y, (y : X) ∈ (B y).source ∧ (B y).source ⊆ W ∧
        (∀ k, (e k).symm.trans (B y) ∈ piecewiseAffineGroupoid V3) ∧
        ∀ z ∈ (B y).source,
          z ∈ f '' old.pieces i ↔ z ∈ R ∧ B y z 0 = 0 ∧ B y z 1 = 0) ∧
      ∀ p ∈ A.vertices, ∃ y : f '' old.pieces i,
        MapsTo (fun z ↦ (g z : X)) (K.closedStar p).space (B y).source ∧
        (K.closedStar p).AffineOnFaces (fun z ↦ B y (g z)) := by
  obtain ⟨s, F, C, K, A, H, g, B, hC, hAC, hCW, hFc, hsep, hK, hAK, hfull,
    hKs, hAs, hH, hg, hgPL, hF, hB, hstar, _, _⟩ :=
    old.exists_component_axis_model_with_raw_branches hf he i P hP hPs hW hAW
  exact ⟨s, F, C, K, A, H, g, B, hC, hAC, hCW, hFc, hsep, hK, hAK, hfull,
    hKs, hAs, hH, hg, hgPL, hF, hB, hstar⟩

end PoincareConjecture.M76.Dehn
