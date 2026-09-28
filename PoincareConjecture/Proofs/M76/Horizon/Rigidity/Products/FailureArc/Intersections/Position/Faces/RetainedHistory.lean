import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Faces.Step
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.AmbientTransport
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolyhedralPLChartHomeomorph
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteFaceCounts



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_finite_planar_triangle_position_with_retained_faces
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    (Source : SimplicialComplex ℝ (ℝ × ℝ)) (hSource : Source.faces.Finite)
    {f : (ℝ × ℝ) → X} (hf : PolyhedralPLInCharts e f Source.space)
    (hfi : InjOn f Source.space)
    (hcover : ∀ y, ∃ i, y ∈ (e i).source)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (g : E → X) (hgc : ContinuousOn g K.space) (hgi : InjOn g K.space)
    (hSV : Disjoint (f '' Source.space) (g '' K.vertices))
    (faces : Finset (K.FaceOfCard 3))
    (hedges : ∀ s ∈ faces, ∀ a ∈ K.faces, a ⊆ s.1 → a.card = 2 →
      (f '' Source.space ∩ (g '' convexHull ℝ (a : Set E))).Finite)
    (hcofaces : ∀ s ∈ faces, ∀ a ∈ K.faces, a ⊆ s.1 → a.card = 2 →
      HasOriginalEdgeCofaceCharts e (f '' Source.space) K g a)
    (mark : Set X)
    (hrim : ∀ x ∈ Source.space, x ∉ interior Source.space → f x ∈ mark)
    (Q : K.FaceOfCard 3 → OpenPartialHomeomorph X V3)
    (hQ : ∀ s ∈ faces, ∀ i, (e i).symm.trans (Q s) ∈ piecewiseAffineGroupoid V3)
    (hQmark : ∀ s ∈ faces, Disjoint (Q s).source mark)
    (A : K.FaceOfCard 3 → E →ᴬ[ℝ] V3)
    (hmap : ∀ s ∈ faces, MapsTo g (convexHull ℝ (s.1 : Set E)) (Q s).source)
    (hA : ∀ s ∈ faces, EqOn ((Q s) ∘ g) (A s) (convexHull ℝ (s.1 : Set E))) :
    ∃ (F : X ≃ₜ X) (W : Set X),
      IsOpen W ∧ EqOn F id W ∧ EqOn F id mark ∧
      (∀ a ∈ K.faces, a.card ≤ 3 → (∀ s ∈ faces, s.1 ≠ a) →
        g '' convexHull ℝ (a : Set E) ⊆ W) ∧
      (∀ a ∈ K.faces, a.card ≤ 2 → g '' convexHull ℝ (a : Set E) ⊆ W) ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      PolyhedralPLInCharts e (F ∘ f) Source.space ∧
      (∀ x ∈ Source.space, x ∉ interior Source.space → F (f x) = f x) ∧
      ∀ s ∈ faces, InTriangleGraphPosition (Q s) (F '' (f '' Source.space))
        (g '' convexHull ℝ (s.1 : Set E)) (convexHull ℝ ((A s) '' (s.1 : Set E))) := by
  classical
  let sk : Set X := ⋃ a ∈ K.faces, ⋃ (_ : a.card ≤ 2), g '' convexHull ℝ (a : Set E)
  have hvertex : g '' K.vertices ⊆ sk := by
    rintro _ ⟨v, hv, rfl⟩
    exact mem_iUnion₂.mpr ⟨{v}, hv, mem_iUnion.mpr ⟨by simp, by simp⟩⟩
  have hedge (a : Finset E) (ha : a ∈ K.faces) (ha2 : a.card ≤ 2) :
      g '' convexHull ℝ (a : Set E) ⊆ sk :=
    fun _ hx => mem_iUnion₂.mpr ⟨a, ha, mem_iUnion.mpr ⟨ha2, hx⟩⟩
  have hid : ∀ i j, (e i).symm.trans
      ((Homeomorph.refl X).toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3 := by
    intro i j
    change (e i).symm.trans ((OpenPartialHomeomorph.refl X).trans (e j)) ∈ _
    simpa only [OpenPartialHomeomorph.refl_trans] using he i j
  have hstage : ∀ t : Finset (K.FaceOfCard 3), t ⊆ faces →
      ∃ (F : X ≃ₜ X) (W : Set X),
        IsOpen W ∧ sk ⊆ W ∧ EqOn F id W ∧ EqOn F id mark ∧
        (∀ a ∈ K.faces, a.card ≤ 3 → (∀ s ∈ faces, s.1 ≠ a) →
          g '' convexHull ℝ (a : Set E) ⊆ W) ∧
        (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
          piecewiseAffineGroupoid V3) ∧
        (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
          piecewiseAffineGroupoid V3) ∧
        ∀ s ∈ t, InTriangleGraphPosition (Q s) (F '' (f '' Source.space))
          (g '' convexHull ℝ (s.1 : Set E)) (convexHull ℝ ((A s) '' (s.1 : Set E))) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨Homeomorph.refl X, univ, isOpen_univ, subset_univ _,
        fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ _ => subset_univ _, hid, hid, by simp⟩
    | @insert s t hst ih =>
      intro hsub
      have hsfaces := hsub (Finset.mem_insert_self s t)
      obtain ⟨F, W, hW, hskW, hfix, hmark, hotherW, hFPL, hFinv, hpositions⟩ :=
        ih (fun _ hx => hsub (Finset.mem_insert_of_mem hx))
      have hFW (x : X) (hx : x ∈ W) :
          x ∈ F '' (f '' Source.space) ↔ x ∈ f '' Source.space := by
        constructor
        · rintro ⟨y, hy, hyx⟩
          exact F.injective (hyx.trans (hfix hx).symm) ▸ hy
        · exact fun hxS => ⟨x, hxS, hfix hx⟩
      have hFimage : (F ∘ f) '' Source.space = F '' (f '' Source.space) :=
        (image_image F f Source.space).symm
      have hFsource := hf.comp_chart_homeomorph Source hSource F hcover hFPL
      have hFvertices : Disjoint ((F ∘ f) '' Source.space) (g '' K.vertices) := by
        rw [hFimage]
        exact disjoint_left.mpr (fun x hx hv => disjoint_left.mp hSV
          ((hFW x (hskW (hvertex hv))).mp hx) hv)
      have hFedge (a : Finset E) (ha : a ∈ K.faces) (has : a ⊆ s.1) (ha2 : a.card = 2) :
          ((F ∘ f) '' Source.space ∩ g '' convexHull ℝ (a : Set E)).Finite := by
        have hh : (F ∘ f) '' Source.space ∩ g '' convexHull ℝ (a : Set E) =
            f '' Source.space ∩ g '' convexHull ℝ (a : Set E) := by
          rw [hFimage]
          ext x
          exact and_congr_left (fun hx => hFW x (hskW (hedge a ha ha2.le hx)))
        rw [hh]
        exact hedges s hsfaces a ha has ha2
      have hFcoface (a : Finset E) (ha : a ∈ K.faces) (has : a ⊆ s.1) (ha2 : a.card = 2) :
          HasOriginalEdgeCofaceCharts e ((F ∘ f) '' Source.space) K g a := by
        rw [hFimage]
        apply (hcofaces s hsfaces a ha has ha2).image_of_disjoint_support F hW.isClosed_compl
        · exact disjoint_left.mpr (fun x hx hxe => hx (hskW (hedge a ha ha2.le hxe)))
        · simpa only [compl_compl] using hfix
      have hFinterior (x : ℝ × ℝ) (hx : x ∈ Source.space)
          (hxQ : (F ∘ f) x ∈ (Q s).source) : x ∈ interior Source.space := by
        by_contra hn
        have hxm := hrim x hx hn
        change F (f x) ∈ (Q s).source at hxQ
        rw [hmark hxm] at hxQ
        exact disjoint_left.mp (hQmark s hsfaces) hxQ hxm
      obtain ⟨Phi, V, hV, hPhiV, hPhiOut, hfacesV, hPhiPL, hPhiInv, hposition⟩ :=
        exists_planar_triangle_position_step Source hSource hFsource
          (fun x hx y hy hxy => hfi hx hy (F.injective hxy)) he
          K hK g hgc hgi hFvertices s.2.1 s.2.2
          hFedge hFcoface
          (Q s) (hQ s hsfaces) hFinterior (A s) (hmap s hsfaces) (hA s hsfaces)
      have hskV : sk ⊆ V := by
        intro x hx
        obtain ⟨a, ha, hx⟩ := mem_iUnion₂.mp hx
        obtain ⟨ha2, hx⟩ := mem_iUnion.mp hx
        exact hfacesV a ha (by omega) (fun h => by rw [h, s.2.2] at ha2; omega) hx
      have hPhiMark : EqOn Phi id mark := fun x hx =>
        hPhiOut (fun hxQ => disjoint_left.mp (hQmark s hsfaces) hxQ hx)
      let F' := F.trans Phi
      have himage (B : Set X) : F' '' B = Phi '' (F '' B) := by
        rw [image_image]
        rfl
      obtain ⟨hF'PL, hF'Inv⟩ := original_PL_motion_trans_both
        e hcover F Phi hFPL hFinv hPhiPL hPhiInv
      refine ⟨F', W ∩ V, hW.inter hV, subset_inter hskW hskV, ?_, ?_, ?_,
        hF'PL, hF'Inv, ?_⟩
      · intro x hx
        change Phi (F x) = x
        simpa only [hfix hx.1, id_eq] using hPhiV hx.2
      · intro x hx
        change Phi (F x) = x
        simpa only [hmark hx, id_eq] using hPhiMark hx
      · intro a ha ha3 hnot
        exact subset_inter (hotherW a ha ha3 hnot)
          (hfacesV a ha ha3 (hnot s hsfaces).symm)
      · intro q hq
        rcases Finset.mem_insert.mp hq with hqs | hqt
        · subst q
          simpa only [himage, hFimage] using hposition
        · have hqs : q.1 ≠ s.1 := by
            intro hh
            exact hst (Subtype.ext hh ▸ hqt)
          have hh := (hpositions q hqt).image_of_fixed Phi hV
            (hfacesV q.1 q.2.1 q.2.2.le hqs) hPhiV
          simpa only [himage] using hh
  obtain ⟨F, W, hW, hskW, hfix, hmark, hotherW, hFPL, hFinv, hpositions⟩ :=
    hstage faces (Subset.refl _)
  exact ⟨F, W, hW, hfix, hmark, hotherW, fun a ha ha2 => (hedge a ha ha2).trans hskW,
    hFPL, hFinv, hf.comp_chart_homeomorph Source hSource F hcover hFPL,
    fun x hx hn => hmark (hrim x hx hn), hpositions⟩

end PoincareConjecture.M76
