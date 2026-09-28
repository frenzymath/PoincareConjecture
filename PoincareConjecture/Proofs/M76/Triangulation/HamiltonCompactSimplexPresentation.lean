import PoincareConjecture.Proofs.M76.Mathlib.CompactPLNeighborhoodModel
import PoincareConjecture.Proofs.M76.Mathlib.FineSimplicialSubdivision
import PoincareConjecture.Proofs.M76.Mathlib.ConvexAffineInjectivity










set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

variable {M E V ι : Type*} [TopologicalSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]




theorem exists_finite_old_chart_simplex_presentation
    (e : ι → OpenPartialHomeomorph M E) {C : Set M}
    (K : SimplicialComplex ℝ V) (hK : K.faces.Finite) (H : C ≃ₜ K.space)
    (hproj : ∀ x : C, ∃ (i : ι) (U : Set M) (a : V →ᴬ[ℝ] E),
      IsOpen U ∧ (x : M) ∈ U ∧ U ⊆ (e i).source ∧
      ∀ y : C, (y : M) ∈ U → e i y = a (H y)) :
    ∃ (L : SimplicialComplex ℝ V) (G : L.space ≃ₜ C),
      L.faces.Finite ∧ L.IsSubdivision K ∧
      ∀ s ∈ L.faces, ∃ (i : ι) (a : V →ᴬ[ℝ] E),
        (∀ y : L.space, (y : V) ∈ convexHull ℝ (s : Set V) →
          (G y : M) ∈ (e i).source ∧ e i (G y) = a y) ∧
        InjOn a (convexHull ℝ (s : Set V)) ∧
        AffineIndependent ℝ (fun y : s => a y) := by
  classical
  choose i U a hU hxU hUs ha using hproj
  let W : C → Set K.space := fun x => (fun y => (H.symm y : M)) ⁻¹' U x
  have hW (x : C) : IsOpen (W x) :=
    (hU x).preimage (continuous_subtype_val.comp H.symm.continuous)
  have hcover (y : K.space) : ∃ x, y ∈ W x := ⟨H.symm y, hxU (H.symm y)⟩
  obtain ⟨L, hL, hLK, hstars⟩ := K.exists_finite_subdivision_stars hK W hW hcover
  let G : L.space ≃ₜ C := (Homeomorph.setCongr hLK.space_eq).trans H.symm
  refine ⟨L, G, hL, hLK, ?_⟩
  intro s hs
  obtain ⟨p, hp⟩ := L.nonempty_of_mem_faces hs
  have hpL : {p} ∈ L.faces :=
    L.down_closed hs (Finset.singleton_subset_iff.mpr hp) (Finset.singleton_nonempty p)
  obtain ⟨x, hstar⟩ := hstars p hpL
  have hsstar : s ∈ (L.closedFaceStar {p}).faces := by
    refine ⟨hs, ?_⟩
    simpa only [Finset.singleton_union, Finset.insert_eq_of_mem hp] using hs
  have hpatch (y : L.space) (hy : (y : V) ∈ convexHull ℝ (s : Set V)) :
      (G y : M) ∈ U x :=
    hstar ⟨y, hLK.space_eq ▸ y.property⟩
      ((L.closedFaceStar {p}).convexHull_subset_space hsstar hy)
  have hformula (y : L.space) (hy : (y : V) ∈ convexHull ℝ (s : Set V)) :
      e (i x) (G y) = a x y := by
    calc
      e (i x) (G y) = a x (H (G y)) := ha x (G y) (hpatch y hy)
      _ = a x y := by
        change a x (H (H.symm ((Homeomorph.setCongr hLK.space_eq) y))) = a x y
        rw [H.apply_symm_apply]
        rfl
  have hinj : InjOn (a x) (convexHull ℝ (s : Set V)) := by
    intro y hy z hz heq
    let y' : L.space := ⟨y, L.convexHull_subset_space hs hy⟩
    let z' : L.space := ⟨z, L.convexHull_subset_space hs hz⟩
    have hcoord : e (i x) (G y') = e (i x) (G z') :=
      (hformula y' hy).trans (heq.trans (hformula z' hz).symm)
    have hpoints : G y' = G z' := Subtype.ext
      ((e (i x)).injOn (hUs x (hpatch y' hy)) (hUs x (hpatch z' hz)) hcoord)
    exact congrArg Subtype.val (G.injective hpoints)
  refine ⟨i x, a x, fun y hy => ⟨hUs x (hpatch y hy), hformula y hy⟩, hinj, ?_⟩
  apply (a x).toAffineMap.affineIndependent_comp_of_injOn_convexHull (L.indep hs)
  change InjOn (a x) (convexHull ℝ (range ((↑) : s → V)))
  rw [show range ((↑) : s → V) = (s : Set V) from Subtype.range_coe]
  exact hinj




theorem exists_compact_old_chart_simplex_presentation
    [T2Space M] [LocallyCompactSpace M] [FiniteDimensional ℝ E]
    (e : ι → OpenPartialHomeomorph M E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (hcover : ∀ x : M, ∃ i, x ∈ (e i).source)
    {A W : Set M} (hA : IsCompact A) (hW : IsOpen W) (hAW : A ⊆ W) :
    ∃ (t : Finset A) (C : Set M) (L : SimplicialComplex ℝ (t → ℝ × E))
      (G : L.space ≃ₜ C), IsCompact C ∧ A ⊆ interior C ∧ C ⊆ W ∧
      L.faces.Finite ∧
      ∀ s ∈ L.faces, ∃ (i : ι) (a : (t → ℝ × E) →ᴬ[ℝ] E),
        (∀ y : L.space, (y : t → ℝ × E) ∈ convexHull ℝ (s : Set (t → ℝ × E)) →
          (G y : M) ∈ (e i).source ∧ e i (G y) = a y) ∧
        InjOn a (convexHull ℝ (s : Set (t → ℝ × E))) ∧
        AffineIndependent ℝ (fun y : s => a y) := by
  classical
  obtain ⟨t, F, C, K, H, hC, hAC, hCW, hK, _, _, hHF, hproj⟩ :=
    exists_compact_PL_neighborhood_model e hcompat hcover hA hW hAW
  have hproj' (x : C) : ∃ (i : ι) (U : Set M) (a : (t → ℝ × E) →ᴬ[ℝ] E),
      IsOpen U ∧ (x : M) ∈ U ∧ U ⊆ (e i).source ∧
      ∀ y : C, (y : M) ∈ U → e i y = a (H y) := by
    obtain ⟨i, U, a, hU, hx, hUs, ha⟩ := hproj x x.property
    refine ⟨i, U, a, hU, hx, hUs, fun y hy => ?_⟩
    rw [hHF y]
    exact (ha hy).symm
  obtain ⟨L, G, hL, _, hfaces⟩ :=
    exists_finite_old_chart_simplex_presentation e K hK H hproj'
  exact ⟨t, C, L, G, hC, hAC, hCW, hL, hfaces⟩

end OpenPartialHomeomorph
