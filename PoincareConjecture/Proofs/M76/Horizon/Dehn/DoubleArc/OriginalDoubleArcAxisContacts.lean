import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcTubeAxis
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricSurfaceIncidence









set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

theorem original_vertex_mem_dual_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : SimplicialComplex ℝ E) [Fintype K.faces]
    {p : E} (hp : p ∈ K.vertices) (s : Finset E) :
    p ∈ (K.barycentricDualBlock s).space ↔ s ⊆ {p} := by
  classical
  have hpB := K.vertices_subset_barycentricSubdivision_vertices hp
  constructor
  · intro hx
    obtain ⟨f, hf, hpf⟩ := mem_space_iff.mp hx
    have hmem := (K.barycentricSubdivision.vertex_mem_convexHull_iff hpB hf.1).mp hpf
    obtain ⟨t, ht, hst, htp⟩ := hf.2 p hmem
    have hcent : t.centroid ℝ id = ({p} : Finset E).centroid ℝ id := by
      simpa only [Finset.centroid_singleton, id_eq] using htp
    have htEq : t = {p} := congrArg Subtype.val
      (K.faceCentroid_injective (a₁ := ⟨t, ht⟩) (a₂ := ⟨{p}, hp⟩) hcent)
    exact htEq ▸ hst
  · intro hs
    apply (K.barycentricDualBlock s).vertices_subset_space
    exact ⟨hpB, fun x hx => by
      have hxp : x = p := Finset.mem_singleton.mp hx
      subst x
      exact ⟨{p}, hp, hs, Finset.centroid_singleton ℝ id p⟩⟩

local notation "I" => Icc (0 : ℝ) 1

theorem original_axis_endpoint_labels
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K A Fr : SimplicialComplex ℝ E) [Fintype K.faces]
    (hAK : A ≤ K) (hFrK : Fr ≤ K)
    (b : I ≃ₜ A.space)
    (hcontact : A.space ∩ Fr.space =
      {(b ⟨0, ⟨le_rfl, zero_le_one⟩⟩ : E),
        (b ⟨1, ⟨zero_le_one, le_rfl⟩⟩ : E)})
    {n : ℕ} (p : Fin (n + 2) → E) (t : Fin (n + 3) → I)
    (hp : Function.Injective p) (ht : StrictMono t)
    (ht0 : t 0 = ⟨0, ⟨le_rfl, zero_le_one⟩⟩)
    (ht1 : t (Fin.last (n + 2)) = ⟨1, ⟨zero_le_one, le_rfl⟩⟩)
    (hverts : A.vertices = range p)
    (hsub : ∀ i : Fin (n + 2), Icc (t i.castSucc : ℝ) (t i.succ : ℝ) ⊆ I)
    (axis : ∀ i : Fin (n + 2), Icc (t i.castSucc : ℝ) (t i.succ : ℝ) ≃ₜ
      ↥((K.barycentricDualBlock {p i}).space ∩ A.space))
    (hkeep : ∀ i x, (axis i x : E) = (b ⟨x, hsub i x.property⟩ : E)) :
    p 0 = (b ⟨0, ⟨le_rfl, zero_le_one⟩⟩ : E) ∧
    p (Fin.last (n + 1)) = (b ⟨1, ⟨zero_le_one, le_rfl⟩⟩ : E) ∧
    ∀ i, p i ∈ Fr.vertices ↔ i = 0 ∨ i = Fin.last (n + 1) := by
  classical
  have hfinite : (A.space ∩ Fr.space).Finite := by
    rw [hcontact]
    exact (finite_singleton _).insert _
  have hzeroFr : (b ⟨0, ⟨le_rfl, zero_le_one⟩⟩ : E) ∈ Fr.space :=
    (hcontact.symm.subset (mem_insert _ _)).2
  have honeFr : (b ⟨1, ⟨zero_le_one, le_rfl⟩⟩ : E) ∈ Fr.space :=
    (hcontact.symm.subset (mem_insert_of_mem _ (mem_singleton _))).2
  have hzero := mem_vertices_of_finite_subcomplex_intersection hAK hFrK hfinite
    (b ⟨0, ⟨le_rfl, zero_le_one⟩⟩).property hzeroFr
  have hone := mem_vertices_of_finite_subcomplex_intersection hAK hFrK hfinite
    (b ⟨1, ⟨zero_le_one, le_rfl⟩⟩).property honeFr
  have hlower (i : Fin (n + 2)) : (b (t i.castSucc) : E) ∈
      (K.barycentricDualBlock {p i}).space := by
    let x : Icc (t i.castSucc : ℝ) (t i.succ : ℝ) :=
      ⟨t i.castSucc, le_rfl, (ht Fin.castSucc_lt_succ).le⟩
    have hx := (axis i x).property.1
    rwa [hkeep i x] at hx
  have hupper (i : Fin (n + 2)) : (b (t i.succ) : E) ∈
      (K.barycentricDualBlock {p i}).space := by
    let x : Icc (t i.castSucc : ℝ) (t i.succ : ℝ) :=
      ⟨t i.succ, (ht Fin.castSucc_lt_succ).le, le_rfl⟩
    have hx := (axis i x).property.1
    rwa [hkeep i x] at hx
  have hp0 : p 0 = (b ⟨0, ⟨le_rfl, zero_le_one⟩⟩ : E) := by
    have hx := hlower 0
    rw [Fin.castSucc_zero, ht0] at hx
    have hs := (original_vertex_mem_dual_iff K (hAK hzero.1) {p 0}).mp hx
    exact Finset.mem_singleton.mp (hs (Finset.mem_singleton_self _))
  have hp1 : p (Fin.last (n + 1)) = (b ⟨1, ⟨zero_le_one, le_rfl⟩⟩ : E) := by
    have hx := hupper (Fin.last (n + 1))
    rw [show (Fin.last (n + 1)).succ = Fin.last (n + 2) from Fin.ext rfl, ht1] at hx
    have hs := (original_vertex_mem_dual_iff K (hAK hone.1) {p (Fin.last (n + 1))}).mp hx
    exact Finset.mem_singleton.mp (hs (Finset.mem_singleton_self _))
  refine ⟨hp0, hp1, ?_⟩
  intro i
  constructor
  · intro hi
    have hiA : p i ∈ A.space := A.vertices_subset_space
      (hverts.symm.subset (mem_range_self i))
    have hh := hcontact.subset ⟨hiA, Fr.vertices_subset_space hi⟩
    rw [← hp0, ← hp1] at hh
    rcases hh with hh | hh
    · exact Or.inl (hp hh)
    · exact Or.inr (hp (mem_singleton_iff.mp hh))
  · rintro (rfl | rfl)
    · exact hp0 ▸ hzero.2
    · exact hp1 ▸ hone.2

end PoincareConjecture.M76.Dehn
