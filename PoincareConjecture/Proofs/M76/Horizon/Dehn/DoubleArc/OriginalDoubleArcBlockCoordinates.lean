import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcTubeFaces

set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)

open Classical in
theorem original_vertex_block_coordinate_marks
    {E X κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {R A : Set X}
    (S : Fin 2 → Set X) (K : SimplicialComplex ℝ E) [Fintype K.faces]
    (g : E → X) (M : κ → SimplicialComplex ℝ E) [∀ i, Fintype (M i).faces]
    (hMK : ∀ i, M i ≤ K) (reg arc : κ) (sheet : Fin 2 → κ)
    (hreg : ∀ z ∈ K.space, z ∈ (M reg).space ↔ g z ∈ R)
    (harc : ∀ z ∈ K.space, z ∈ (M arc).space ↔ g z ∈ A)
    (hsheet : ∀ i z, z ∈ K.space → (z ∈ (M (sheet i)).space ↔ g z ∈ S i))
    (v : (M arc).vertices) (B : OpenPartialHomeomorph X V3)
    (hsource : MapsTo g (K.closedStar v).space B.source)
    (haxis : ∀ y ∈ B.source, y ∈ A ↔ y ∈ R ∧ B y 0 = 0 ∧ B y 1 = 0)
    (hsheets : ∀ i y, y ∈ B.source → (y ∈ S i ↔ y ∈ R ∧ B y i.castSucc = 0)) :
    let V := K.barycentricDualBlock {(v : E)}
    let D := (M reg).barycentricDualBlock {(v : E)}
    (∀ i z, z ∈ D.space → (z ∈ (M (sheet i)).space ↔ B (g z) i.castSucc = 0)) ∧
    {z | z ∈ D.space ∧ B (g z) 0 = 0 ∧ B (g z) 1 = 0} = V.space ∩ (M arc).space := by
  classical
  let V := K.barycentricDualBlock {(v : E)}
  let D := (M reg).barycentricDualBlock {(v : E)}
  have hvK : (v : E) ∈ K.vertices := hMK arc v.property
  have hVK : V.space ⊆ K.space :=
    (space_subset_of_le (K.barycentricDualBlock_le {(v : E)})).trans
      K.barycentricSubdivision_isSubdivision.space_eq.subset
  have hVB : MapsTo g V.space B.source := by
    intro z hz
    obtain ⟨s, hs, hzs⟩ := mem_space_iff.mp hz
    obtain ⟨t, ht, hst⟩ := K.exists_original_star_face_of_vertex_dual_face hvK hs
    exact hsource ((K.closedStar v).convexHull_subset_space ht (hst hzs))
  have hD : D.space = V.space ∩ (M reg).space :=
    (K.barycentricDualBlock_space_inter_subcomplex (M reg) (hMK reg) {(v : E)}).symm
  have hDV : D.space ⊆ V.space := hD.subset.trans inter_subset_left
  have hDR {z : E} (hz : z ∈ D.space) : g z ∈ R :=
    (hreg z (hVK (hDV hz))).mp (hD.subset hz).2
  refine ⟨?_, ?_⟩
  · intro i z hz
    rw [hsheet i z (hVK (hDV hz)), hsheets i (g z) (hVB (hDV hz))]
    exact and_iff_right (hDR hz)
  · ext z
    constructor
    · rintro ⟨hz, h0, h1⟩
      exact ⟨hDV hz, (harc z (hVK (hDV hz))).mpr
        ((haxis (g z) (hVB (hDV hz))).mpr ⟨hDR hz, h0, h1⟩)⟩
    · rintro ⟨hzV, hzA⟩
      have h := (haxis (g z) (hVB hzV)).mp ((harc z (hVK hzV)).mp hzA)
      exact ⟨hD.superset ⟨hzV, (hreg z (hVK hzV)).mpr h.1⟩, h.2⟩

end PoincareConjecture.M76.Dehn
