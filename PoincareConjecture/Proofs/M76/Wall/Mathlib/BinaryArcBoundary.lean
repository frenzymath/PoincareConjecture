import PoincareConjecture.Proofs.M76.Wall.Mathlib.BinaryVertexLinks
import PoincareConjecture.Proofs.M76.Wall.Mathlib.ArcNeighborhoodBoundaryContact
import PoincareConjecture.Proofs.M76.Wall.Mathlib.ArcDualBoundaryAvoidance
import PoincareConjecture.Proofs.M76.Wall.Mathlib.EdgeChainFaces

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

theorem image_arc_chain_boundary_binaryLevel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K A D : SimplicialComplex ℝ E) [Fintype K.faces] [Fintype D.faces]
    (hAK : A ≤ K) (hDK : D ≤ K)
    (hfullA : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ A.vertices) → s ∈ A.faces)
    (hfullD : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ D.vertices) → s ∈ D.faces)
    (hcard : ∀ s ∈ A.faces, s.card ≤ 2)
    {n : ℕ} (p : Fin (n + 2) → E) (hinj : Function.Injective p)
    (hverts : A.vertices = range p)
    (hedge : ∀ i : Fin (n + 1), {p i.castSucc, p i.succ} ∈ A.faces)
    (hcover : A.space = ⋃ i : Fin (n + 1), segment ℝ (p i.castSucc) (p i.succ))
    (hcontact : A.space ∩ D.space = {p 0, p (Fin.last (n + 1))})
    {F : E → E} {h : E → ℝ}
    (hF : K.barycentricSubdivision.AffineOnFaces F) (hh : K.AffineOnFaces h)
    (hcenters : ∀ s : K.faces, F (s.val.centroid ℝ id) = s.val.binaryFaceCenter A.vertices)
    (hvalues : ∀ v ∈ K.vertices,
      (v ∈ A.vertices → h v = 1) ∧ (v ∉ A.vertices → h v = 0))
    (hmarks : ∀ L : SimplicialComplex ℝ E, L ≤ K → F '' L.space = L.space) :
    let T := fun i : Fin (n + 2) =>
      ((K.barycentricDualBlock {p i}).link (p i)).space ∪
        (D.barycentricDualBlock {p i}).space
    let J := fun i : Fin (n + 1) => (K.barycentricDualBlock {p i.castSucc, p i.succ}).space
    let Q := fun i : Fin (n + 1) =>
      ((K.barycentricDualBlock {p i.castSucc, p i.succ}).link
        (({p i.castSucc, p i.succ} : Finset E).centroid ℝ id)).space
    F '' ((⋃ i, T i) \ ⋃ i, J i \ Q i) =
      (K.space ∩ {x | h x = (1 / 2 : ℝ)}) ∪
        (F '' (D.barycentricDualBlock {p 0}).space ∪
          F '' (D.barycentricDualBlock {p (Fin.last (n + 1))}).space) := by
  classical
  let B := fun i : Fin (n + 2) => (K.barycentricDualBlock {p i}).space
  let V := fun i : Fin (n + 2) => ((K.barycentricDualBlock {p i}).link (p i)).space
  let d := fun i : Fin (n + 2) => (D.barycentricDualBlock {p i}).space
  let T := fun i : Fin (n + 2) => V i ∪ d i
  let J := fun i : Fin (n + 1) => (K.barycentricDualBlock {p i.castSucc, p i.succ}).space
  let Q := fun i : Fin (n + 1) =>
    ((K.barycentricDualBlock {p i.castSucc, p i.succ}).link
      (({p i.castSucc, p i.succ} : Finset E).centroid ℝ id)).space
  let N := (K.barycentricNeighborhood A).space
  have hp (i : Fin (n + 2)) : p i ∈ A.vertices := by
    rw [hverts]
    exact mem_range_self i
  have hpne : p 0 ≠ p (Fin.last (n + 1)) := by
    intro he
    have hv := congrArg Fin.val (hinj he)
    change 0 = n + 1 at hv
    omega
  have hecard (i : Fin (n + 1)) : ({p i.castSucc, p i.succ} : Finset E).card = 2 := by
    have hne : p i.castSucc ≠ p i.succ := by
      intro he
      have hv := congrArg Fin.val (hinj he)
      change i.val = i.val + 1 at hv
      omega
    simp [hne]
  have hfinite : (A.space ∩ D.space).Finite := by
    rw [hcontact]
    exact (finite_singleton _).insert _
  have hNB : N = ⋃ i, B i := by
    change (K.barycentricNeighborhood A).space = ⋃ i, B i
    rw [K.barycentricNeighborhood_space_eq_iUnion_dualBlocks, hverts]
    ext x
    constructor
    · intro hx
      obtain ⟨v, ⟨i, rfl⟩, hxi⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion.mpr ⟨i, hxi⟩
    · intro hx
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      exact mem_iUnion₂.mpr ⟨p i, mem_range_self i, hxi⟩
  have hBN (i : Fin (n + 2)) : B i ⊆ N := by
    rw [hNB]
    exact subset_iUnion B i
  have hVB (i : Fin (n + 2)) : V i ⊆ B i :=
    space_subset_of_le (fun _ hs => hs.1)
  have hdND (i : Fin (n + 2)) : d i ⊆ N ∩ D.space := by
    intro x hx
    have hm := (K.barycentricDualBlock_space_inter_subcomplex D hDK {p i}).symm.subset hx
    exact ⟨hBN i hm.1, hm.2⟩
  have hfeet : N ∩ D.space = d 0 ∪ d (Fin.last (n + 1)) :=
    (K.arc_neighborhood_boundary_contact A D hAK hDK hfullA hpne hcontact).1
  have himageN : F '' N = K.space ∩ {x | (1 / 2 : ℝ) ≤ h x} :=
    K.image_barycentricNeighborhood_binaryCenters A hF hcenters hh hvalues
  have hlevels (i : Fin (n + 1)) :
      F '' Q i = (F '' J i) ∩ {x | h x = (1 / 2 : ℝ)} ∧
        F '' (J i \ Q i) = (F '' J i) ∩ {x | (1 / 2 : ℝ) < h x} := by
    apply K.image_dualBlock_link_binaryLevel A hAK hfullA hF hh hcenters hvalues hmarks
      (hedge i)
    intro s hs hes
    exact (Finset.eq_of_subset_of_card_le hes (by rw [hecard i]; exact hcard s hs)).symm
  have hDavoid (x : E) (hxD : x ∈ D.space) : x ∉ ⋃ i, J i \ Q i := by
    intro hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    have hdisj := (K.arc_edge_dual_disjoint_boundary A D hAK hDK hfullD hfinite
      (hedge i) (hecard i)).1
    exact Set.disjoint_left.mp hdisj hxi.1 hxD
  have hdT (i : Fin (n + 2)) : d i ⊆ (⋃ i, T i) \ ⋃ i, J i \ Q i := by
    intro x hx
    exact ⟨mem_iUnion.mpr ⟨i, Or.inr hx⟩, hDavoid x (hdND i hx).2⟩
  change F '' ((⋃ i, T i) \ ⋃ i, J i \ Q i) =
    (K.space ∩ {x | h x = (1 / 2 : ℝ)}) ∪ (F '' d 0 ∪ F '' d (Fin.last (n + 1)))
  ext y
  constructor
  · rintro ⟨x, ⟨hxT, hxnot⟩, rfl⟩
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxT
    rcases hxi with hxV | hxd
    · have hxN : x ∈ N := hBN i (hVB i hxV)
      have hFx := himageN.subset ⟨x, hxN, rfl⟩
      by_cases heq : h (F x) = (1 / 2 : ℝ)
      · exact Or.inl ⟨hFx.1, heq⟩
      · have hhigh : (1 / 2 : ℝ) < h (F x) := lt_of_le_of_ne hFx.2 (Ne.symm heq)
        obtain ⟨s, hs, hscard, _, hxJ⟩ := (K.binary_vertex_link_levels A hAK hfullA hcard
          hF hh hcenters hvalues hmarks (hp i)).2 x hxV hhigh
        obtain ⟨_, j, hsub⟩ := (A.faces_of_edge_chain_cover p hedge hcover s).mp hs
        have hsJ : s = {p j.castSucc, p j.succ} :=
          Finset.eq_of_subset_of_card_le hsub (by rw [hecard j, hscard])
        apply False.elim (hxnot ?_)
        apply mem_iUnion.mpr
        refine ⟨j, ?_⟩
        simpa only [hsJ] using hxJ
    · have hxfoot := hfeet.subset (hdND i hxd)
      rcases hxfoot with hx₀ | hx₁
      · exact Or.inr (Or.inl ⟨x, hx₀, rfl⟩)
      · exact Or.inr (Or.inr ⟨x, hx₁, rfl⟩)
  · rintro (hy | hy)
    · obtain ⟨x, hxN, hxy⟩ := himageN.superset ⟨hy.1, by
        change (1 / 2 : ℝ) ≤ h y
        exact le_of_eq (Eq.symm hy.2)⟩
      have hxlevel : h (F x) = (1 / 2 : ℝ) := by rw [hxy]; exact hy.2
      have hxB : x ∈ ⋃ i, B i := hNB ▸ hxN
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hxB
      have hxV : x ∈ V i := (K.binary_vertex_link_levels A hAK hfullA hcard
        hF hh hcenters hvalues hmarks (hp i)).1 ⟨hxi, hxlevel⟩
      refine ⟨x, ⟨mem_iUnion.mpr ⟨i, Or.inl hxV⟩, ?_⟩, hxy⟩
      intro hxJ
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hxJ
      have hhigher := ((hlevels j).2.subset ⟨x, hxj, rfl⟩).2
      exact hhigher.ne' hxlevel
    · rcases hy with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
      · exact ⟨x, hdT 0 hx, rfl⟩
      · exact ⟨x, hdT (Fin.last (n + 1)) hx, rfl⟩

end Geometry.SimplicialComplex
