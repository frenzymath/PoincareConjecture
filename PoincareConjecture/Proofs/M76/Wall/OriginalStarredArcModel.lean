import PoincareConjecture.Proofs.M76.Wall.OriginalArcNeighborhoodModel
import PoincareConjecture.Proofs.M76.Wall.OriginalArcComplexDimension

set_option autoImplicit false

open Set Metric Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

open Classical in

theorem PLDomain.exists_starred_arc_model
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {L : Set X}
    (he : PLDomain e L) (hL : IsCompact L)
    {q : ℝ → X} (hq : PolyhedralPLInCharts e q I) (hqi : InjOn q I)
    (hzero : q 0 ∈ frontier L) (hone : q 1 ∈ frontier L)
    (hproper : ∀ t ∈ Ioo (0 : ℝ) 1, q t ∉ L)
    {W : Set X} (hW : IsOpen W) (hqW : MapsTo q I W)
    (U : Fin 2 → Set X) (hU : ∀ i, IsOpen (U i))
    (hU0 : q 0 ∈ U 0) (hU1 : q 1 ∈ U 1)
    (S : Fin 2 → Set X) (hsphere : ∀ i, ChartwisePLSphere e (S i))
    (hSL : ∀ i, S i ⊆ frontier L) :
    ∃ (s : Finset (L ∪ q '' I : Set X)) (F : X → (s → ℝ × V3)) (C : Set X)
      (K : SimplicialComplex ℝ (s → ℝ × V3))
      (A : Fin 5 → SimplicialComplex ℝ (s → ℝ × V3))
      (H : C ≃ₜ K.space) (g : (s → ℝ × V3) → C) (b : I ≃ₜ (A 2).space),
      IsCompact C ∧ L ∪ q '' I ⊆ interior C ∧ Continuous F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      K.faces.Finite ∧
      (∀ i, A i ≤ K ∧ (A i).faces.Finite ∧
        ∀ t ∈ K.faces, (∀ v ∈ t, v ∈ (A i).vertices) → t ∈ (A i).faces) ∧
      K.space = F '' C ∧ (A 0).space = F '' L ∧
      (A 1).space = F '' frontier L ∧ (A 2).space = F '' (q '' I) ∧
      (A 3).space = F '' S 0 ∧ (A 4).space = F '' S 1 ∧
      (∀ x : C, (H x : s → ℝ × V3) = F x) ∧
      ContinuousOn g K.space ∧
      (∀ z : K.space, (g z : X) = (H.symm z : X)) ∧
      PolyhedralPLInCharts e (fun z => (g z : X)) K.space ∧
      b.IsFinitePL ∧ (∀ t : I, (b t : s → ℝ × V3) = F (q t)) ∧
      (∀ t ∈ (A 2).faces, t.card ≤ 2) ∧
      (∀ x ∈ C, ∃ (i : ι) (V : Set X) (a : (s → ℝ × V3) →ᴬ[ℝ] V3),
        IsOpen V ∧ x ∈ V ∧ V ⊆ (e i).source ∧ EqOn (a ∘ F) (e i) V) ∧
      ∀ p ∈ (A 2).vertices, ∃ G : OpenPartialHomeomorph X V3,
        MapsTo (fun z => (g z : X)) (K.closedStar p).space G.source ∧
        (K.closedStar p).AffineOnFaces (fun z => G (g z)) ∧
        (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
        G.source ⊆ interior C ∩ W ∧
        ((G.source ⊆ Lᶜ ∧ ∃ v : V3, v ≠ 0 ∧
          ∀ y ∈ G.source, y ∈ q '' I ↔ ∃ r : ℝ, G y = r • v) ∨
        ∃ (i : Fin 2) (A : V3 →L[ℝ] ℝ) (v : V3),
          G.source ⊆ U i ∧ A v = 1 ∧
          (∀ y ∈ G.source, y ∈ L ↔ 0 ≤ A (G y)) ∧
          (∀ y ∈ G.source, y ∈ frontier L ↔ A (G y) = 0) ∧
          ∀ y ∈ G.source,
            y ∈ q '' I ↔ ∃ r : ℝ, r ≤ 0 ∧ G y = r • v) := by
  classical
  obtain ⟨s, F, C, K0, A0, H0, g, b0, hC, hcore, hFc, hFPL, hK0, hA0,
    hK0s, hA00, hA01, hA02, hA03, hA04, hH0, hgc, hg, hgPL, hb0, hb0val, hproj⟩ :=
    he.exists_arc_neighborhood_model hL hq hqi S hsphere hSL
  have hqC (t : ℝ) (ht : t ∈ I) : q t ∈ C :=
    interior_subset (hcore (Or.inr ⟨t, ht, rfl⟩))
  have hgF (x : X) (hx : x ∈ C) : (g (F x) : X) = x := by
    have h := hg (H0 ⟨x, hx⟩)
    rw [H0.symm_apply_apply] at h
    simpa only [hH0] using h
  have hginj : InjOn (fun z => (g z : X)) K0.space := by
    intro x hx y hy hxy
    have hi : H0.symm ⟨x, hx⟩ = H0.symm ⟨y, hy⟩ :=
      Subtype.ext ((hg ⟨x, hx⟩).symm.trans (hxy.trans (hg ⟨y, hy⟩)))
    exact congrArg Subtype.val (H0.symm.injective hi)
  have hgarc : MapsTo (fun z => (g z : X)) (A0 2).space (q '' I) := by
    intro z hz
    obtain ⟨x, ⟨t, ht, rfl⟩, rfl⟩ := hA02.subset hz
    exact ⟨t, ht, (hgF (q t) (hqC t ht)).symm⟩
  have hqWC : MapsTo q I (interior C ∩ W) :=
    fun t ht => ⟨hcore (Or.inr ⟨t, ht, rfl⟩), hqW ht⟩
  obtain ⟨K, A, hK, hKK0, hA, hdim, hstars⟩ :=
    he.exists_original_arc_complex_dimension hq hqi hzero hone hproper
      (isOpen_interior.inter hW) hqWC U hU hU0 hU1 K0 hK0 hgPL hginj
      A0 (fun i => (hA0 i).2.1) (fun i => space_subset_of_le (hA0 i).1) 2 hgarc
  let H : C ≃ₜ K.space := H0.trans (Homeomorph.setCongr hKK0.space_eq.symm)
  let b : I ≃ₜ (A 2).space := b0.trans (Homeomorph.setCongr (hA 2).2.1.symm)
  have hb : b.IsFinitePL := hb0.trans
    (Homeomorph.isFinitePL_setCongr (hA 2).2.1.symm (A 2)
      (hK.subset (hA 2).1) (hA 2).2.1)
  refine ⟨s, F, C, K, A, H, g, b, hC, hcore, hFc, hFPL, hK,
    fun i => ⟨(hA i).1, hK.subset (hA i).1, (hA i).2.2⟩,
    hKK0.space_eq.trans hK0s, (hA 0).2.1.trans hA00, (hA 1).2.1.trans hA01,
    (hA 2).2.1.trans hA02, (hA 3).2.1.trans hA03, (hA 4).2.1.trans hA04,
    fun x => hH0 x, ?_, ?_, ?_, hb, fun t => hb0val t, hdim, hproj, hstars⟩
  · rwa [hKK0.space_eq]
  · intro z
    exact hg ⟨z, hKK0.space_eq.subset z.property⟩
  · rwa [hKK0.space_eq]

end PoincareConjecture.M76
