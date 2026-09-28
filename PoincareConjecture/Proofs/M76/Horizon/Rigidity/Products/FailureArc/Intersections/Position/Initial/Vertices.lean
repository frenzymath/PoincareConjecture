import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Initial.Point
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalPLMotionComposition



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_protected_planar_vertex_position
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {Z : Set X}
    (Source : SimplicialComplex ℝ (ℝ × ℝ)) (hSource : Source.faces.Finite)
    {f : (ℝ × ℝ) → X} (hf : PolyhedralPLInCharts e f Source.space)
    (hcover : ∀ y, ∃ i, y ∈ (e i).source)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hZ : IsClosed Z) (V : Finset X)
    (hprotected : Disjoint (f '' Source.space ∩ Z) (V : Set X)) :
    ∃ (F : X ≃ₜ X) (C : Set X),
      IsCompact C ∧ Disjoint C Z ∧ EqOn F id Cᶜ ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      PolyhedralPLInCharts e (F ∘ f) Source.space ∧
      Disjoint (F '' (f '' Source.space)) (V : Set X) := by
  classical
  have hid : ∀ i j, (e i).symm.trans
      ((Homeomorph.refl X).toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3 := by
    intro i j
    change (e i).symm.trans ((OpenPartialHomeomorph.refl X).trans (e j)) ∈ _
    simpa only [OpenPartialHomeomorph.refl_trans] using he i j
  revert hprotected
  induction V using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨Homeomorph.refl X, ∅, isCompact_empty, by simp, fun _ _ => rfl,
      hid, hid, hf.comp_chart_homeomorph Source hSource _ hcover hid, by simp⟩
  | @insert p V hpV ih =>
    intro hprotected
    obtain ⟨F, C, hC, hCZ, hFout, hFPL, hFinv, hfF, hFV⟩ :=
      ih (hprotected.mono_right (by intro x hx; exact Finset.mem_insert_of_mem hx))
    by_cases hpS : p ∈ F '' (f '' Source.space)
    · have hpZ : p ∉ Z := by
        intro hpZ
        obtain ⟨x, hx, hxp⟩ := hpS
        have hpC : p ∉ C := fun hc => disjoint_left.mp hCZ hc hpZ
        have hFp : F p = p := hFout hpC
        have hxp' : x = p := F.injective (hxp.trans hFp.symm)
        exact disjoint_left.mp hprotected ⟨hxp' ▸ hx, hpZ⟩ (Finset.mem_insert_self _ _)
      let U : Set X := Zᶜ ∩ (V : Set X)ᶜ
      have hU : IsOpen U := hZ.isOpen_compl.inter V.finite_toSet.isClosed.isOpen_compl
      obtain ⟨G, D, hD, hDU, hGout, hGPL, hGinv, _, hpG⟩ :=
        exists_planar_surface_point_avoiding_motion Source hSource hfF
          hcover he hU (show p ∈ U from ⟨hpZ, hpV⟩)
      have hDZ : Disjoint D Z := disjoint_left.mpr fun x hx hz => (hDU hx).1 hz
      have hfixed (x : X) (hx : x ∈ (V : Set X)) : G x = x :=
        hGout (fun h => (hDU h).2 hx)
      have hPL := original_PL_motion_trans e hcover F G hFPL hGPL
      have hinv := original_PL_motion_trans e hcover G.symm F.symm hGinv hFinv
      have himage : (F.trans G) '' (f '' Source.space) = G '' ((F ∘ f) '' Source.space) := by
        rw [image_image, image_image]
        rfl
      refine ⟨F.trans G, C ∪ D, hC.union hD, disjoint_union_left.mpr ⟨hCZ, hDZ⟩,
        ?_, hPL, hinv, hf.comp_chart_homeomorph Source hSource _ hcover hPL, ?_⟩
      · intro x hx
        change G (F x) = x
        rw [hFout (fun h => hx (Or.inl h))]
        exact hGout (fun h => hx (Or.inr h))
      · apply disjoint_left.mpr
        intro x hx hxV
        rcases Finset.mem_insert.mp hxV with hxp | hxV
        · exact hpG (hxp ▸ himage.subset hx)
        · obtain ⟨y, hy, hxy⟩ := hx
          have hFy : F y = x := G.injective (hxy.trans (hfixed x hxV).symm)
          exact disjoint_left.mp hFV ⟨y, hy, hFy⟩ hxV
    · refine ⟨F, C, hC, hCZ, hFout, hFPL, hFinv, hfF, ?_⟩
      apply disjoint_left.mpr
      intro x hx hxV
      rcases Finset.mem_insert.mp hxV with hxp | hxV
      · exact hpS (hxp ▸ hx)
      · exact disjoint_left.mp hFV hx hxV

end PoincareConjecture.M76
