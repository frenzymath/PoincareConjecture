import PoincareConjecture.Proofs.M76.Mathlib.RadialRescalingHomeomorph

set_option autoImplicit false

open Set NormedSpace Geometry

namespace AbstractSimplicialComplex

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def IsRadialEmbedding (A : AbstractSimplicialComplex ι) (v : ι → E) : Prop :=
  Function.Injective v ∧ ∃ L : SimplicialComplex ℝ E,
    L.faces = {t : Finset E | ∃ s ∈ A.faces, (t : Set E) = v '' (s : Set ι)} ∧
    (∀ t ∈ L.faces, LinearIndependent ℝ ((↑) : t → E)) ∧
    InjOn (NormedSpace.normalize : E → E) L.space

abbrev RadialEmbedding (A : AbstractSimplicialComplex ι) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] := {v : ι → E // A.IsRadialEmbedding v}

variable {A : AbstractSimplicialComplex ι} {v : ι → E}

private theorem vertices_eq_range_of_faces {L : SimplicialComplex ℝ E}
    (hfaces : L.faces = {t : Finset E | ∃ s ∈ A.faces, (t : Set E) = v '' (s : Set ι)}) :
    L.vertices = range v := by
  ext y
  constructor
  · intro hy
    change {y} ∈ L.faces at hy
    rw [hfaces] at hy
    obtain ⟨s, _, he⟩ := hy
    have hmem : y ∈ v '' (s : Set ι) := he ▸ (by simp : y ∈ ({y} : Finset E))
    obtain ⟨i, _, hi⟩ := hmem
    exact ⟨i, hi⟩
  · rintro ⟨i, rfl⟩
    change {v i} ∈ L.faces
    rw [hfaces]
    exact ⟨{i}, A.singleton_mem i, by simp⟩

theorem IsRadialEmbedding.ne_zero (hv : A.IsRadialEmbedding v) (i : ι) : v i ≠ 0 := by
  obtain ⟨L, hfaces, hlin, _⟩ := hv.2
  have hvertex : v i ∈ L.vertices := by
    rw [vertices_eq_range_of_faces hfaces]
    exact mem_range_self i
  intro hi
  apply (hlin {v i} hvertex).zero_notMem_convexHull
  simp [hi]

theorem IsRadialEmbedding.pos_smul (hv : A.IsRadialEmbedding v)
    (r : E → ℝ) (hr : ∀ i, 0 < r (v i)) :
    A.IsRadialEmbedding (fun i => r (v i) • v i) := by
  classical
  obtain ⟨L, hfaces, hlin, hinj⟩ := hv.2
  have hvertices := vertices_eq_range_of_faces hfaces
  have hpos : ∀ x ∈ L.vertices, 0 < r x := by
    intro x hx
    rw [hvertices] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hr i
  have hvinj := SimplicialComplex.injOn_pos_smul_vertices hinj r hpos
  refine ⟨fun i j hij => hv.1 (hvinj ?_ ?_ hij), L.radialRescale hlin hinj r hpos, ?_,
    fun _ hs => SimplicialComplex.linearIndependent_radialRescale_face hlin hinj r hpos hs,
    SimplicialComplex.injOn_normalize_radialRescale hlin hinj r hpos⟩
  · rw [hvertices]
    exact mem_range_self i
  · rw [hvertices]
    exact mem_range_self j
  · ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [hfaces] at hu
      obtain ⟨s, hs, hus⟩ := hu
      exact ⟨s, hs, by simp only [Finset.coe_image, hus, Set.image_image]⟩
    · rintro ⟨s, hs, hts⟩
      refine ⟨s.image v, ?_, ?_⟩
      · rw [hfaces]
        exact ⟨s, hs, Finset.coe_image⟩
      · apply Finset.coe_injective
        simpa only [Finset.coe_image, Set.image_image] using hts.symm

theorem IsRadialEmbedding.normalize (hv : A.IsRadialEmbedding v) :
    A.IsRadialEmbedding (fun i => NormedSpace.normalize (v i)) :=
  hv.pos_smul (fun x => ‖x‖⁻¹) (fun i => inv_pos.mpr (norm_pos_iff.mpr (hv.ne_zero i)))

end AbstractSimplicialComplex
