import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteTerminalPair
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLImageTriangulation
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedInterval
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedraSubcomplexes
import PoincareConjecture.Proofs.M76.RelativeApproximation.InteriorSourceModel
import PoincareConjecture.Proofs.M76.RelativeApproximation.ModelInverse
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CubePrismBoundary











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3}

private theorem sphere_graph_image
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S : Set X} (s : ChartwisePLSphere e S) (F : X → E)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) :
    ∃ J : SimplicialComplex ℝ E, J.faces.Finite ∧ J.space = F '' S := by
  obtain ⟨K, hK, hKs⟩ := exists_finite_unitCubeSphere (ι := Fin 3)
  have hsK : PolyhedralPLInCharts e s.map K.space := hKs.symm ▸ s.piecewiseAffine
  obtain ⟨J, hJ, hJs⟩ :=
    (hsK.finitePiecewiseAffineOn_comp K hK hF).exists_finite_triangulation_image
  have himage : s.map '' sphere (0 : V3) 1 = S := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      rw [s.map_eq ⟨z, hz⟩]
      exact (s.parametrization ⟨z, hz⟩).property
    · intro x hx
      obtain ⟨z, hz⟩ := s.parametrization.surjective ⟨x, hx⟩
      exact ⟨z, z.property, (s.map_eq z).trans (congrArg Subtype.val hz)⟩
  refine ⟨J, hJ, ?_⟩
  rw [hJs, hKs, image_comp, himage]

variable [T2Space X]






theorem PLDomain.exists_arc_neighborhood_model
    {L : Set X} (he : PLDomain e L) (hL : IsCompact L)
    {q : ℝ → X} (hq : PolyhedralPLInCharts e q I) (hqi : InjOn q I)
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
      ∀ x ∈ C, ∃ (i : ι) (V : Set X) (a : (s → ℝ × V3) →ᴬ[ℝ] V3),
        IsOpen V ∧ x ∈ V ∧ V ⊆ (e i).source ∧ EqOn (a ∘ F) (e i) V := by
  classical
  let : LocallyCompactSpace X := he.locallyCompactSpace
  have hcore : IsCompact (L ∪ q '' I) :=
    hL.union (isCompact_Icc.image_of_continuousOn hq.continuousOn)
  obtain ⟨s, F, C, K0, H0, hC, hcoreC, _, hK0, hFc, hF, hH0, hproj⟩ :=
    OpenPartialHomeomorph.exists_compact_PL_neighborhood_model
      e he.compatible he.cover hcore isOpen_univ (subset_univ _)
  have hLC : L ⊆ C := fun _ hx => interior_subset (hcoreC (Or.inl hx))
  have hqC : MapsTo q I C := fun _ ht =>
    interior_subset (hcoreC (Or.inr ⟨_, ht, rfl⟩))
  have hFinj : InjOn F C := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H0.injective (Subtype.ext
      ((hH0 ⟨x, hx⟩).trans (hxy.trans (hH0 ⟨y, hy⟩).symm))))
  have hK0s : K0.space = F '' C := by
    apply Subset.antisymm
    · intro z hz
      refine ⟨H0.symm ⟨z, hz⟩, (H0.symm ⟨z, hz⟩).property, ?_⟩
      exact (hH0 (H0.symm ⟨z, hz⟩)).symm.trans
        (congrArg Subtype.val (H0.apply_symm_apply ⟨z, hz⟩))
    · rintro _ ⟨x, hx, rfl⟩
      rw [← hH0 ⟨x, hx⟩]
      exact (H0 ⟨x, hx⟩).property
  obtain ⟨P0, B0, _, hP0, _, hB0, hP0s, hB0s, _, _⟩ :=
    OpenPartialHomeomorph.exists_finite_PL_domain_image_pair
      e he.cover hFc hF hL (hFinj.mono hLC) he.halfspace
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨T, hT, hTI, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one)
  have hqT : PolyhedralPLInCharts e q T.space := hTI.symm ▸ hq
  have hFq : FinitePiecewiseAffineOn (F ∘ q) I := by
    simpa only [hTI] using hqT.finitePiecewiseAffineOn_comp T hT hF
  obtain ⟨Pq, hPq, hPqs⟩ := hFq.exists_finite_triangulation_image
  obtain ⟨b0, hb0, hb0val⟩ := hFq.exists_homeomorph_image
    (fun x hx y hy hxy => hqi hx hy (hFinj (hqC hx) (hqC hy) hxy))
  obtain ⟨S0, hS0, hS0s⟩ := sphere_graph_image (hsphere 0) F hF
  obtain ⟨S1, hS1, hS1s⟩ := sphere_graph_image (hsphere 1) F hF
  let J : Fin 5 → SimplicialComplex ℝ (s → ℝ × V3) := ![P0, B0, Pq, S0, S1]
  have hJ : ∀ i, (J i).faces.Finite := by
    intro i
    fin_cases i
    · exact hP0
    · exact hB0
    · exact hPq
    · exact hS0
    · exact hS1
  have hJK : ∀ i, (J i).space ⊆ K0.space := by
    intro i
    rw [hK0s]
    fin_cases i
    · change P0.space ⊆ F '' C
      rw [hP0s]
      exact image_mono hLC
    · change B0.space ⊆ F '' C
      rw [hB0s]
      exact image_mono (he.closed.frontier_subset.trans hLC)
    · change Pq.space ⊆ F '' C
      rw [hPqs, image_comp]
      exact image_mono (image_subset_iff.mpr hqC)
    · change S0.space ⊆ F '' C
      rw [hS0s]
      exact image_mono ((hSL 0).trans (he.closed.frontier_subset.trans hLC))
    · change S1.space ⊆ F '' C
      rw [hS1s]
      exact image_mono ((hSL 1).trans (he.closed.frontier_subset.trans hLC))
  obtain ⟨K, A, hK, hKK0, hA⟩ :=
    K0.exists_subdivision_with_finite_full_polyhedra hK0 J hJ hJK
  let H : C ≃ₜ K.space := H0.trans (Homeomorph.setCongr hKK0.space_eq.symm)
  have hHF (x : C) : (H x : s → ℝ × V3) = F x := hH0 x
  have hA0 : (A 0).space = F '' L := (hA 0).2.1.trans hP0s
  have hA1 : (A 1).space = F '' frontier L := (hA 1).2.1.trans hB0s
  have hA2 : (A 2).space = (F ∘ q) '' I := (hA 2).2.1.trans hPqs
  have hA3 : (A 3).space = F '' S 0 := (hA 3).2.1.trans hS0s
  have hA4 : (A 4).space = F '' S 1 := (hA 4).2.1.trans hS1s
  let b : I ≃ₜ (A 2).space := b0.trans (Homeomorph.setCongr hA2.symm)
  have hb : b.IsFinitePL := hb0.trans
    (Homeomorph.isFinitePL_setCongr hA2.symm (A 2) (hK.subset (hA 2).1) hA2)
  have hbval (t : I) : (b t : s → ℝ × V3) = F (q t) := hb0val t
  let x0 : C := ⟨q 0, hqC ⟨le_rfl, zero_le_one⟩⟩
  obtain ⟨g, hgc, hg, hgPL⟩ :=
    exists_polyhedral_PL_model_inverse e K hK H F (Subset.refl C) x0 hHF hproj
  refine ⟨s, F, C, K, A, H, g, b, hC, hcoreC, hFc, hF, hK, ?_,
    hKK0.space_eq.trans hK0s, hA0, hA1, ?_, hA3, hA4, hHF, hgc, hg,
    hgPL, hb, hbval, hproj⟩
  · exact fun i => ⟨(hA i).1, hK.subset (hA i).1, (hA i).2.2⟩
  · rw [hA2, image_comp]

end PoincareConjecture.M76
