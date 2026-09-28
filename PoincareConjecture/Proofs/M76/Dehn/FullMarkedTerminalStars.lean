import PoincareConjecture.Proofs.M76.PrimeReduction.CompatibleChartStars
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalDomainCharts
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalChartStarPurity
import PoincareConjecture.Proofs.M76.RelativeApproximation.ModelInverse
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLImageTriangulation

set_option autoImplicit false

open Set Geometry

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)

variable {U G X ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [DecidableEq G] [TopologicalSpace X]

theorem exists_full_marked_pair_chart_stars
    {e : ι → OpenPartialHomeomorph X V3} {N : Set X}
    (he : PoincareConjecture.M76.PLDomain e N)
    (S : SimplicialComplex ℝ U) (hS : S.faces.Finite)
    {f : U → X} (hf : PolyhedralPLInCharts e f S.space) (v0 : S.space)
    (hfN : MapsTo f S.space N)
    (F : X → G)
    (hFPL : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (K0 L0 : SimplicialComplex ℝ G) (hK0 : K0.faces.Finite) (hL0K : L0 ≤ K0)
    (hK0s : K0.space = F '' N) (hL0s : L0.space = F '' frontier N)
    (J0 : N ≃ₜ K0.space) (hJF : ∀ x : N, (J0 x : G) = F x)
    (hproj : ∀ x ∈ N, ∃ (i : ι) (V : Set X) (a : G →ᴬ[ℝ] V3),
      IsOpen V ∧ x ∈ V ∧ V ⊆ (e i).source ∧ EqOn (a ∘ F) (e i) V) :
    ∃ (K : SimplicialComplex ℝ G) (A : Fin 2 → SimplicialComplex ℝ G)
      (J : N ≃ₜ K.space) (g : G → N),
      K.faces.Finite ∧ K.IsSubdivision K0 ∧
      (∀ a, A a ≤ K ∧ (A a).faces.Finite ∧
        ∀ t ∈ K.faces, (∀ v ∈ t, v ∈ (A a).vertices) → t ∈ (A a).faces) ∧
      K.space = F '' N ∧ (A 0).space = F '' frontier N ∧
      (A 1).space = F '' (f '' S.space) ∧
      (∀ x : N, (J x : G) = F x) ∧
      ContinuousOn g K.space ∧
      (∀ z : K.space, (g z : X) = (J.symm z : X)) ∧
      PolyhedralPLInCharts e (fun z => (g z : X)) K.space ∧
      (∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph X V3,
        MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
        (K.closedStar p).AffineOnFaces (fun z => B (g z)) ∧
        (B.source ⊆ N ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
          ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ N ↔ 0 ≤ ell (B y))) ∧
      ∀ t ∈ K.faces, ∃ u ∈ K.faces, t ⊆ u ∧ u.card = 4 := by
  classical
  obtain ⟨D0, hD0, hD0s⟩ :=
    (hf.finitePiecewiseAffineOn_comp S hS hFPL).exists_finite_triangulation_image
  have hD0s' : D0.space = F '' (f '' S.space) := by
    rw [hD0s, image_image]
    rfl
  let A0 : Fin 2 → SimplicialComplex ℝ G := ![L0, D0]
  have hA0 (a : Fin 2) : (A0 a).faces.Finite := by
    fin_cases a
    · exact hK0.subset hL0K
    · exact hD0
  have hA0K (a : Fin 2) : (A0 a).space ⊆ K0.space := by
    fin_cases a
    · exact SimplicialComplex.space_subset_of_le hL0K
    · change D0.space ⊆ K0.space
      rw [hD0s', hK0s]
      exact image_mono (image_subset_iff.mpr hfN)
  let x0 : N := ⟨f v0, hfN v0.property⟩
  obtain ⟨g, hgc, hgval, hgPL⟩ :=
    PoincareConjecture.M76.exists_polyhedral_PL_model_inverse e K0 hK0 J0 F
      (subset_refl N) x0 hJF hproj
  choose B hBpoint hBcompat hBkind using
    fun q : K0.space => he.exists_local_region_chart (g q)
  obtain ⟨K, A, hK, hKK0, hA, hstars⟩ :=
    hgPL.exists_full_compatible_chart_stars K0 hK0 B hBcompat hBpoint A0 hA0 hA0K
  let J : N ≃ₜ K.space := J0.trans (Homeomorph.setCongr hKK0.space_eq.symm)
  have hJF' (x : N) : (J x : G) = F x := hJF x
  have hgval' (z : K.space) : (g z : X) = (J.symm z : X) :=
    hgval ⟨z, hKK0.space_eq.subset z.property⟩
  have hgc' : ContinuousOn g K.space := hKK0.space_eq.symm ▸ hgc
  have hgPL' : PolyhedralPLInCharts e (fun z => (g z : X)) K.space :=
    hKK0.space_eq.symm ▸ hgPL
  have hstars' (p : G) (hp : p ∈ K.vertices) :
      ∃ B : OpenPartialHomeomorph X V3,
        MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
        (K.closedStar p).AffineOnFaces (fun z => B (g z)) ∧
        (B.source ⊆ N ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
          ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ N ↔ 0 ≤ ell (B y)) := by
    obtain ⟨q, hmap, hface⟩ := hstars p hp
    refine ⟨B q, hmap, hBcompat q, hface, ?_⟩
    rcases hBkind q with hint | ⟨ell, v, hv, _, hhalf⟩
    · exact Or.inl hint
    · exact Or.inr ⟨ell, v, hv, hhalf⟩
  refine ⟨K, A, J, g, hK, hKK0,
    fun a => ⟨(hA a).1, hK.subset (hA a).1, (hA a).2.2⟩,
    hKK0.space_eq.trans hK0s, (hA 0).2.1.trans hL0s,
    (hA 1).2.1.trans hD0s', hJF', hgc', hgval', hgPL', hstars', ?_⟩
  apply PoincareConjecture.M76.exists_tetrahedral_coface_of_original_chart_stars K hK J g hgval'
  intro p hp
  obtain ⟨B, hsource, _, hface, hregion⟩ := hstars' p hp
  exact ⟨B, hsource, hface, hregion⟩

end Geometry.OriginalPLTower
