import PoincareConjecture.Proofs.M76.Rigidity.DiskGraphParameter
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteTerminalPair
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedraSubcomplexes
import PoincareConjecture.Proofs.M76.Mathlib.SupportedFinitePLExtension
import PoincareConjecture.Proofs.M76.RelativeApproximation.InteriorSourceModel
import PoincareConjecture.Proofs.M76.RelativeApproximation.ModelInverse

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

theorem exists_intrinsic_proper_disk_neighborhood_model
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (hR : IsCompact R) (he : PLDomain e R) {j : V2 → X}
    (hj : PolyhedralPLInCharts e j D)
    (hemb : Topology.IsEmbedding (fun z : D => j z))
    (hDR : MapsTo j D R)
    (hproper : ∀ z : D, j z ∈ frontier R ↔ (z : V2) ∈ Q) :
    ∃ (s : Finset R) (F : X → (s → ℝ × V3)) (C : Set X)
      (K : SimplicialComplex ℝ (s → ℝ × V3))
      (A : Fin 4 → SimplicialComplex ℝ (s → ℝ × V3))
      (H : C ≃ₜ K.space) (g : (s → ℝ × V3) → C) (u : (s → ℝ × V3) → V2),
      IsCompact C ∧ R ⊆ interior C ∧ Continuous F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      K.faces.Finite ∧
      (∀ i, A i ≤ K ∧ (A i).faces.Finite ∧
        ∀ t ∈ K.faces, (∀ v ∈ t, v ∈ (A i).vertices) → t ∈ (A i).faces) ∧
      K.space = F '' C ∧ (A 0).space = F '' R ∧
      (A 1).space = F '' frontier R ∧ (A 2).space = F '' (j '' D) ∧
      (A 3).space = F '' (j '' Q) ∧
      (A 2).space ∩ (A 1).space = (A 3).space ∧
      (∀ x : C, (H x : s → ℝ × V3) = F x) ∧
      ContinuousOn g K.space ∧
      (∀ z : K.space, (g z : X) = (H.symm z : X)) ∧
      PolyhedralPLInCharts e (fun z => (g z : X)) K.space ∧
      K.AffineOnFaces u ∧ (∀ z : D, u (F (j z)) = (z : V2)) ∧
      ∀ x ∈ C, ∃ (i : ι) (V : Set X) (a : (s → ℝ × V3) →ᴬ[ℝ] V3),
        IsOpen V ∧ x ∈ V ∧ V ⊆ (e i).source ∧ EqOn (a ∘ F) (e i) V := by
  classical
  let : LocallyCompactSpace X := he.locallyCompactSpace
  obtain ⟨s, F, C, K0, H0, hC, hRCint, _, hK0, hFc, hF, hH0, hproj⟩ :=
    OpenPartialHomeomorph.exists_compact_PL_neighborhood_model
      e he.compatible he.cover hR isOpen_univ (subset_univ _)
  have hRC : R ⊆ C := hRCint.trans interior_subset
  have hFinj : InjOn F C := by
    intro x hx y hy hxy
    have h : H0 ⟨x, hx⟩ = H0 ⟨y, hy⟩ := Subtype.ext
      ((hH0 ⟨x, hx⟩).trans (hxy.trans (hH0 ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (H0.injective h)
  have hK0s : K0.space = F '' C := by
    ext z
    constructor
    · intro hz
      exact ⟨H0.symm ⟨z, hz⟩, (H0.symm ⟨z, hz⟩).property,
        (hH0 (H0.symm ⟨z, hz⟩)).symm.trans
          (congrArg Subtype.val (H0.apply_symm_apply ⟨z, hz⟩))⟩
    · rintro ⟨x, hx, rfl⟩
      rw [← hH0 ⟨x, hx⟩]
      exact (H0 ⟨x, hx⟩).property
  obtain ⟨P0, B0, _, hP0, _, hB0, hP0s, hB0s, _, _⟩ :=
    OpenPartialHomeomorph.exists_finite_PL_domain_image_pair
      e he.cover hFc hF hR (hFinj.mono hRC) he.halfspace
  obtain ⟨P, T, _, u0, hP, hT, hPs, hTs, _, _, hu0, hu0j, hPT⟩ :=
    exists_proper_disk_graph_parameter he hj hemb hDR hproper F hF (hFinj.mono hRC)
  have hPK0 : P.space ⊆ K0.space := by
    rw [hPs, hK0s]
    exact image_mono (image_subset_iff.mpr (fun _ hz => hRC (hDR hz)))
  obtain ⟨u, hu, huu0, _, _⟩ :=
    hu0.exists_supported_extension K0 hK0 hPK0 isOpen_univ (subset_univ _)
  have huj (z : D) : u (F (j z)) = (z : V2) := by
    have hzP : F (j z) ∈ P.space := by
      rw [hPs]
      exact ⟨j z, ⟨z, z.property, rfl⟩, rfl⟩
    exact (huu0 hzP).trans (hu0j z)
  obtain ⟨K1, hK1, hK1s, hufaces⟩ := hu
  let J : Fin 4 → SimplicialComplex ℝ (s → ℝ × V3) := ![P0, B0, P, T]
  have hJ : ∀ i, (J i).faces.Finite := by
    intro i
    fin_cases i
    · exact hP0
    · exact hB0
    · exact hP
    · exact hT
  have hJK1 : ∀ i, (J i).space ⊆ K1.space := by
    intro i
    rw [hK1s, hK0s]
    fin_cases i
    · change P0.space ⊆ F '' C
      rw [hP0s]
      exact image_mono hRC
    · change B0.space ⊆ F '' C
      rw [hB0s]
      exact image_mono (he.closed.frontier_subset.trans hRC)
    · change P.space ⊆ F '' C
      rw [hPs]
      exact image_mono (image_subset_iff.mpr (fun _ hz => hRC (hDR hz)))
    · change T.space ⊆ F '' C
      rw [hTs]
      exact image_mono (image_subset_iff.mpr
        (fun _ hz => hRC (hDR (sphere_subset_closedBall hz))))
  obtain ⟨K, A, hK, hKK1, hA⟩ :=
    K1.exists_subdivision_with_finite_full_polyhedra hK1 J hJ hJK1
  have hKK0 : K.space = K0.space := hKK1.space_eq.trans hK1s
  let H : C ≃ₜ K.space := H0.trans (Homeomorph.setCongr hKK0.symm)
  have hHF (x : C) : (H x : s → ℝ × V3) = F x := hH0 x
  have hA0 : (A 0).space = F '' R := (hA 0).2.1.trans hP0s
  have hA1 : (A 1).space = F '' frontier R := (hA 1).2.1.trans hB0s
  have hA2 : (A 2).space = F '' (j '' D) := (hA 2).2.1.trans hPs
  have hA3 : (A 3).space = F '' (j '' Q) := (hA 3).2.1.trans hTs
  have hAint : (A 2).space ∩ (A 1).space = (A 3).space := by
    rw [hA2, hA1, hA3, ← hPs, ← hTs]
    exact hPT
  let x0 : C := ⟨j 0, hRC (hDR (mem_closedBall_self zero_le_one))⟩
  obtain ⟨g, hgc, hg, hgPL⟩ :=
    exists_polyhedral_PL_model_inverse e K hK H F (Subset.refl C) x0 hHF hproj
  refine ⟨s, F, C, K, A, H, g, u, hC, hRCint, hFc, hF, hK, ?_,
    hKK0.trans hK0s, hA0, hA1, hA2, hA3, hAint, hHF, hgc, hg, hgPL,
    hKK1.affineOnFaces hufaces, huj, hproj⟩
  exact fun i => ⟨(hA i).1, hK.subset (hA i).1, (hA i).2.2⟩

end PoincareConjecture.M76
