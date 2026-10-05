import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Maps.RadialRescalingHomeomorph

/-!
# Radial embeddings in vertex coordinates

A faithful geometric realization whose faces have independent position
vectors and whose carrier has injective central projection is a radial
embedding. Positive radial rescaling preserves this space. This is the
unquotiented vertex space used in Cairns 1940, Section 5, pp. 801--802.
See M76 derivation 18; the star and coordinate-quotient identifications
are separate assertions.
-/

set_option autoImplicit false

open Set NormedSpace Geometry

namespace AbstractSimplicialComplex

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A vertex assignment faithfully realizes an abstract complex by
independent position-vector simplices with injective central projection.
See Cairns pp. 801--802 and M76 derivation 18. -/
def IsRadialEmbedding (A : AbstractSimplicialComplex ι) (v : ι → E) : Prop :=
  Function.Injective v ∧ ∃ L : SimplicialComplex ℝ E,
    L.faces = {t : Finset E | ∃ s ∈ A.faces, (t : Set E) = v '' (s : Set ι)} ∧
    (∀ t ∈ L.faces, LinearIndependent ℝ ((↑) : t → E)) ∧
    InjOn (NormedSpace.normalize : E → E) L.space

/-- Radial vertex embeddings with the subspace topology of the product
of vertex positions. See Cairns p. 801 and M76 derivation 18. -/
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

/-- Every vertex of a radial embedding is nonzero. Requiring every
singleton in the abstract complex makes all coordinates constrained.
See Cairns p. 801 and M76 derivation 18. -/
theorem IsRadialEmbedding.ne_zero (hv : A.IsRadialEmbedding v) (i : ι) : v i ≠ 0 := by
  obtain ⟨L, hfaces, hlin, _⟩ := hv.2
  have hvertex : v i ∈ L.vertices := by
    rw [vertices_eq_range_of_faces hfaces]
    exact mem_range_self i
  intro hi
  apply (hlin {v i} hvertex).zero_notMem_convexHull
  simp [hi]

/-- Positive scaling of each embedded vertex preserves radial
embeddings and their labelled faces. See Cairns Lemma 5.3 and
M76 derivations 17--18. -/
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

/-- Vertex normalization preserves the faithful radial realization.
See Cairns Lemma 5.3 and M76 derivation 18. -/
theorem IsRadialEmbedding.normalize (hv : A.IsRadialEmbedding v) :
    A.IsRadialEmbedding (fun i => NormedSpace.normalize (v i)) :=
  hv.pos_smul (fun x => ‖x‖⁻¹) (fun i => inv_pos.mpr (norm_pos_iff.mpr (hv.ne_zero i)))

end AbstractSimplicialComplex
