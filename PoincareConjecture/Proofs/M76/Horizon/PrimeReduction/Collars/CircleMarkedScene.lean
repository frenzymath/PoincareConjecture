import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.MarkedHalfspaceModel
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Crossings.SelectedChartStars
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.CyclicModelOrder
import PoincareConjecture.Proofs.M76.Mathlib.PolygonCircle

set_option autoImplicit false
open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "Idx" => Sum Bool (Fin 3)

theorem circle_coordinate_identity_pl
    (K : SimplicialComplex ℝ V3) (hK : K.faces.Finite) :
    PolyhedralPLInCharts (fun _ : Unit => OpenPartialHomeomorph.refl V3) id K.space := by
  refine ⟨continuousOn_id, ?_⟩
  intro x
  refine ⟨(), K, univ, hK, Subset.rfl, isOpen_univ, mem_univ _, ?_, ?_, ?_⟩
  · rintro _ ⟨z, _, rfl⟩
    exact z.property
  · exact fun _ _ => mem_univ _
  · exact (K.affineOnFaces_affine (ContinuousAffineMap.id ℝ V3)).finitePiecewiseAffineOn hK

theorem exists_circle_marked_scene
    (P : Fin 3 → SimplicialComplex ℝ V3) (hP : ∀ i, (P i).faces.Finite)
    {m : ℕ} (L : Polygon V3 (m + 3)) (hL : L.HasSimplicialEdges)
    (hLi : Function.Injective L) (hPL : (P 2).space = L.boundary ℝ)
    {W : Set V3} (hW : IsOpen W) (hLW : L.boundary ℝ ⊆ W)
    (hisolate : ∀ x ∈ W, x ∈ L.boundary ℝ ↔ x ∈ (P 0).space ∧ x ∈ (P 1).space)
    (hcharts : ∀ x ∈ L.boundary ℝ, ∃ B : OpenPartialHomeomorph V3 V3,
      x ∈ B.source ∧ B ∈ piecewiseAffineGroupoid V3 ∧
      ∀ (i : Fin 2) y, y ∈ B.source → (y ∈ (P i.castSucc).space ↔ B y i.castSucc = 0)) :
    ∃ (N : SimplicialComplex ℝ V3) (M : Idx → SimplicialComplex ℝ V3)
      (n : ℕ) (p : Fin (n + 3) → V3),
      N.faces.Finite ∧ L.boundary ℝ ⊆ interior N.space ∧ N.space ⊆ W ∧
      (∀ i, M i ≤ N ∧ (M i).faces.Finite ∧
        ∀ f ∈ N.faces, (∀ v ∈ f, v ∈ (M i).vertices) → f ∈ (M i).faces) ∧
      M (.inl false) = N ∧ (M (.inl true)).space = ∅ ∧
      (M (.inr 2)).space = L.boundary ℝ ∧
      (∀ i : Fin 2, (M (.inr i.castSucc)).space = N.space ∩ (P i.castSucc).space) ∧
      Function.Injective p ∧ range p = (M (.inr 2)).vertices ∧
      (∀ s : Finset V3, s ∈ (M (.inr 2)).faces ↔ s.Nonempty ∧
        ∃ j : Fin (n + 3), s ⊆ {p j, p (finRotate (n + 3) j)}) ∧
      ∃ B : (M (.inr 2)).vertices → OpenPartialHomeomorph V3 V3,
        (∀ v, (B v).source ⊆ W ∧ B v ∈ piecewiseAffineGroupoid V3) ∧
        ∀ v : (M (.inr 2)).vertices,
          (N.closedStar v).space ⊆ (B v).source ∧
          (N.closedStar v).AffineOnFaces (B v) ∧
          (∀ y ∈ (B v).source, y ∈ L.boundary ℝ ↔ B v y 0 = 0 ∧ B v y 1 = 0) ∧
          ∀ (i : Fin 2) y, y ∈ (B v).source →
            (y ∈ (P i.castSucc).space ↔ B v y i.castSucc = 0) := by
  classical
  have hcompact : IsCompact (L.boundary ℝ) := L.isCompact_boundary
  have hchartsUniv (x : V3) (_hx : x ∈ W) :
      ∃ Q : OpenPartialHomeomorph V3 V3, x ∈ Q.source ∧
        LocallyPiecewiseAffineOn Q Q.source ∧
        (Q.source ⊆ interior (univ : Set V3) ∨
          ∃ ell : V3 →ᴬ[ℝ] ℝ, ell.toAffineMap.linear ≠ 0 ∧
            ∀ y ∈ Q.source, y ∈ (univ : Set V3) ↔ 0 ≤ ell (Q y)) := by
    refine ⟨OpenPartialHomeomorph.refl V3, mem_univ _, ?_, Or.inl (by simp)⟩
    exact (mem_piecewiseAffineGroupoid_iff_forward _).mp (piecewiseAffineGroupoid V3).id_mem
  obtain ⟨K, M₀, hK, hLK, hKW, hM₀, hreg₀, hfr₀, hsource₀⟩ :=
    exists_marked_local_halfspace_model hcompact hW hLW hchartsUniv P hP
  have hreg₀' : (M₀ (.inl false)).space = K.space := by simpa using hreg₀
  have hfr₀' : (M₀ (.inl true)).space = ∅ := by simpa using hfr₀
  have harc₀ : (M₀ (.inr 2)).space = L.boundary ℝ := by
    rw [hsource₀ 2, inter_univ, hPL]
    exact inter_eq_right.mpr (hLK.trans interior_subset)
  have hsheet₀ (i : Fin 2) : (M₀ (.inr i.castSucc)).space =
      K.space ∩ (P i.castSucc).space := by simpa using hsource₀ i.castSucc
  choose G hpoint hGPL hGsheets using hcharts
  let C : L.boundary ℝ → OpenPartialHomeomorph V3 V3 :=
    fun x => (G x x.property).restrOpen W hW
  have hCpoint (x : L.boundary ℝ) : (x : V3) ∈ (C x).source :=
    ⟨hpoint x x.property, hLW x.property⟩
  have hCPL (x : L.boundary ℝ) : C x ∈ piecewiseAffineGroupoid V3 := by
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    exact ((mem_piecewiseAffineGroupoid_iff_forward _).mp (hGPL x x.property)).mono
      (C x).open_source (fun _ hy => hy.1)
  have hCaxis (x : L.boundary ℝ) (y : V3) (hy : y ∈ (C x).source) :
      y ∈ L.boundary ℝ ↔ C x y 0 = 0 ∧ C x y 1 = 0 := by
    rw [hisolate y hy.2]
    exact and_congr (hGsheets x x.property 0 y hy.1) (hGsheets x x.property 1 y hy.1)
  let e := fun _ : Unit => OpenPartialHomeomorph.refl V3
  have he (i j : Unit) : (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3 := by
    simpa only [e, OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_trans] using
      (piecewiseAffineGroupoid V3).id_mem
  let charts : ↥(K.space ∩ id ⁻¹' L.boundary ℝ) → OpenPartialHomeomorph V3 V3 :=
    fun x => C ⟨x, x.property.2⟩
  have hcompat (x : ↥(K.space ∩ id ⁻¹' L.boundary ℝ)) (i : Unit) :
      (e i).symm.trans (charts x) ∈ piecewiseAffineGroupoid V3 := by
    simpa only [e, OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_trans] using
      hCPL ⟨x, x.property.2⟩
  have hmark : (M₀ (.inr 2)).space = K.space ∩ id ⁻¹' L.boundary ℝ := by
    rw [harc₀]
    exact (inter_eq_right.mpr (hLK.trans interior_subset)).symm
  obtain ⟨N, M, hN, hNK, hM, hstars⟩ := Dehn.exists_selected_compatible_chart_stars
    e he (fun x => ⟨(), mem_univ x⟩) K hK (circle_coordinate_identity_pl K hK)
      hcompact.isClosed charts hcompat (fun x => hCpoint ⟨x, x.property.2⟩)
      M₀ (fun i => (hM₀ i).2.1) (fun i => space_subset_of_le (hM₀ i).1) (.inr 2) hmark
  have harc : (M (.inr 2)).space = L.boundary ℝ := (hM (.inr 2)).2.1.trans harc₀
  have hreg : (M (.inl false)).space = N.space :=
    (hM (.inl false)).2.1.trans (hreg₀'.trans hNK.space_eq.symm)
  have hregEq : M (.inl false) = N := by
    apply le_antisymm (hM (.inl false)).1
    intro s hs
    apply (hM (.inl false)).2.2 s hs
    intro v hv
    have hvN := N.face_subset_vertices hs hv
    have hvM : v ∈ (M (.inl false)).space := hreg.symm.subset (N.vertices_subset_space hvN)
    obtain ⟨t, ht, hvt⟩ := mem_space_iff.mp hvM
    have hvt' := (N.vertex_mem_convexHull_iff hvN ((hM (.inl false)).1 ht)).mp hvt
    exact (M (.inl false)).down_closed ht
      (Finset.singleton_subset_iff.mpr hvt') (Finset.singleton_nonempty _)
  obtain ⟨circle⟩ := L.nonempty_boundary_homeomorph_circle hL hLi
  have hconn : IsConnected (M (.inr 2)).space := by
    rw [harc]
    exact isConnected_iff_connectedSpace.mpr (circle.connectedSpace_iff.mpr inferInstance)
  obtain ⟨n, Q, hQi, _, hQv, _, hQf, _⟩ :=
    (M (.inr 2)).exists_exact_cyclic_polygon_of_polygon_carrier
      (hN.subset (hM (.inr 2)).1) hconn L hL hLi harc.symm
  choose q hqmap hqaff using fun v : (M (.inr 2)).vertices => hstars v v.property
  let B := fun v : (M (.inr 2)).vertices => charts (q v)
  refine ⟨N, M, n, Q, hN, ?_, hNK.space_eq.subset.trans hKW,
    (fun i => ⟨(hM i).1, hN.subset (hM i).1, (hM i).2.2⟩),
    hregEq, (hM (.inl true)).2.1.trans hfr₀', harc, ?_, hQi, hQv, hQf,
    B, ?_, ?_⟩
  · simpa only [hNK.space_eq] using hLK
  · intro i
    exact (hM (.inr i.castSucc)).2.1.trans ((hsheet₀ i).trans (by rw [hNK.space_eq]))
  · intro v
    exact ⟨fun _ hx => hx.2, hCPL ⟨q v, (q v).property.2⟩⟩
  · intro v
    refine ⟨hqmap v, hqaff v, hCaxis ⟨q v, (q v).property.2⟩, ?_⟩
    intro i y hy
    exact hGsheets (q v) (q v).property.2 i y hy.1

end PoincareConjecture.M76
