import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Model.FromDomains
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Products.ModelProduct

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

attribute [local instance] Classical.propDecidable

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (-1 : ℝ) 1

theorem model_inverse_properties
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    {C : Set X} {A : Set E} (H : C ≃ₜ A) (F : X → E) (g : E → C)
    (hF : ∀ x : C, (H x : E) = F x)
    (hg : ∀ z : A, (g z : X) = (H.symm z : X)) :
    InjOn (fun z ↦ (g z : X)) A ∧
      (∀ x ∈ C, (g (F x) : X) = x) ∧ ∀ z ∈ A, F (g z) = z := by
  have hright (z) (hz : z ∈ A) : F (g z) = z := by
    rw [hg ⟨z, hz⟩]
    exact (hF (H.symm ⟨z, hz⟩)).symm.trans
      (congrArg Subtype.val (H.apply_symm_apply ⟨z, hz⟩))
  refine ⟨?_, ?_, hright⟩
  · intro z hz w hw hzw
    exact (hright z hz).symm.trans ((congrArg F hzw).trans (hright w hw))
  · intro x hx
    have heq : F x = (H ⟨x, hx⟩ : E) := (hF ⟨x, hx⟩).symm
    rw [heq, hg, H.symm_apply_apply]

theorem exists_signed_domain_surface_product
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {D W : Set X}
    (hD : IsCompact D) (heD : PLDomain e D)
    (hW : IsCompact W) (heW : PLDomain e W) (hne : (D ∪ W).Nonempty)
    (hcross : ∀ x ∈ frontier D ∩ frontier W,
      ∃ B : OpenPartialHomeomorph X V3,
        x ∈ B.source ∧ B x = 0 ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ B.source, y ∈ frontier D ↔ B y 0 = 0) ∧
        ∀ y ∈ B.source, y ∈ frontier W ↔ B y 1 = 0) :
    ∃ (s : Finset (D ∪ W : Set X)) (F : X → (s → ℝ × V3)) (C : Set X)
      (T : SimplicialComplex.CoorientedSurfaceStars (s → ℝ × V3))
      (H : C ≃ₜ T.ambient.space) (g : (s → ℝ × V3) → C)
      (f : (s → ℝ × V3) × ℝ → (s → ℝ × V3)),
      IsCompact C ∧ D ∪ W ⊆ interior C ∧ Continuous F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      T.ambient.space = F '' C ∧
      (T.marked 0).space = F '' W ∧
      (T.marked 1).space = F '' frontier W ∧
      (T.marked 2).space = F '' (frontier D ∩ W) ∧
      (T.marked 3).space = F '' (frontier D ∩ frontier W) ∧
      (∀ x : C, (H x : s → ℝ × V3) = F x) ∧
      ContinuousOn g T.ambient.space ∧
      (∀ z : T.ambient.space, (g z : X) = (H.symm z : X)) ∧
      PolyhedralPLInCharts e (fun z ↦ (g z : X)) T.ambient.space ∧
      InjOn (fun z ↦ (g z : X)) T.ambient.space ∧
      (∀ x ∈ C, (g (F x) : X) = x) ∧
      (∀ z ∈ T.ambient.space, F (g z) = z) ∧
      FinitePiecewiseAffineOn f ((T.marked 2).space ×ˢ I) ∧
      InjOn f ((T.marked 2).space ×ˢ I) ∧
      MapsTo f ((T.marked 2).space ×ˢ I) T.ambient.space ∧
      f '' ((T.marked 2).space ×ˢ I) =
        ⋃ p : (T.marked 2).vertices, T.dualRegion {(p : s → ℝ × V3)} ∧
      (∀ x ∈ (T.marked 2).space, f (x, 0) = x) ∧
      (∀ z ∈ (T.marked 2).space ×ˢ I, (g (f z) : X) ∈ W) ∧
      (∀ z ∈ (T.marked 2).space ×ˢ I, (g (f z) : X) ∈ D ↔ 0 ≤ z.2) ∧
      (∀ z ∈ (T.marked 2).space ×ˢ I, (g (f z) : X) ∈ frontier D ↔ z.2 = 0) ∧
      ∀ z ∈ (T.marked 2).space ×ˢ I,
        (g (f z) : X) ∈ frontier W ↔ (g z.1 : X) ∈ frontier W := by
  classical
  obtain ⟨s, F, C, T, H, g, B, hC, hDC, hFc, hF, hKs,
    hM0, hM1, hM2, hM3, hHF, hgc, hg, hgPL, _, hcharts⟩ :=
    exists_cooriented_surface_stars_of_domains hD heD hW heW hne hcross
  obtain ⟨f, hf, hfi, himage, hf0, hproper, hpos, hneg⟩ := T.exists_model_product
  obtain ⟨hgi, hleft, hright⟩ := model_inverse_properties H F g hHF hg
  have hWC : W ⊆ C := fun _ hx ↦ interior_subset (hDC (Or.inr hx))
  have hFWC : frontier W ⊆ C := heW.closed.frontier_subset.trans hWC
  have hmem (S : Set X) (hSC : S ⊆ C) (z) (hz : z ∈ T.ambient.space) :
      z ∈ F '' S ↔ (g z : X) ∈ S := by
    constructor
    · rintro ⟨y, hy, heq⟩
      have hyz : (g z : X) = y := heq ▸ hleft y (hSC hy)
      exact hyz.symm ▸ hy
    · intro hzS
      exact ⟨g z, hzS, hright z hz⟩
  have htarget (z) (hz : z ∈ (T.marked 2).space ×ˢ I) :
      ∃ p : (T.marked 2).vertices, f z ∈ T.dualRegion {(p : s → ℝ × V3)} :=
    mem_iUnion.mp (himage.subset ⟨z, hz, rfl⟩)
  have hfA : MapsTo f ((T.marked 2).space ×ˢ I) T.ambient.space := by
    intro z hz
    obtain ⟨p, hp⟩ := htarget z hz
    exact T.star_subset_ambient p (T.dualRegion_subset_star p (Finset.mem_singleton_self _) hp)
  refine ⟨s, F, C, T, H, g, f, hC, hDC, hFc, hF, hKs, hM0, hM1, hM2, hM3,
    hHF, hgc, hg, hgPL, hgi, hleft, hright, hf, hfi, hfA, himage, hf0, ?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨p, hp⟩ := htarget z hz
    exact (hmem W hWC (f z) (hfA hz)).mp (hM0.subset hp.2)
  · intro z hz
    obtain ⟨p, hp⟩ := htarget z hz
    have hstar := T.dualRegion_subset_star p (Finset.mem_singleton_self _) hp
    exact ((hcharts p).2.2.2.1 _ hstar).trans (hpos p z hz hstar)
  · intro z hz
    obtain ⟨p, hp⟩ := htarget z hz
    have hstar := T.dualRegion_subset_star p (Finset.mem_singleton_self _) hp
    apply ((hcharts p).2.2.2.2 _ hstar).trans
    constructor
    · intro hh
      exact le_antisymm ((hneg p z hz hstar).mp hh.le) ((hpos p z hz hstar).mp hh.ge)
    · intro ht
      exact le_antisymm ((hneg p z hz hstar).mpr ht.le) ((hpos p z hz hstar).mpr ht.ge)
  · intro z hz
    have hzA := SimplicialComplex.space_subset_of_le (T.marked_le 2) hz.1
    have htargetW := hmem (frontier W) hFWC (f z) (hfA hz)
    have hbaseW := hmem (frontier W) hFWC z.1 hzA
    rw [← hM1] at htargetW hbaseW
    exact htargetW.symm.trans ((hproper z hz).trans hbaseW)

end PoincareConjecture.M76
