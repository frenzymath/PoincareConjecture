import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.SourceRefinement



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.CollarMesh
local notation "E" => ((ℝ × ℝ) × ℝ)

theorem exists_common_subdivision_of_finite_family
    {D κ : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    (K : SimplicialComplex ℝ D) (hK : K.faces.Finite)
    (s : Finset κ) (J : κ → SimplicialComplex ℝ D)
    (hJ : ∀ i ∈ s, (J i).faces.Finite) (hJK : ∀ i ∈ s, (J i).IsSubdivision K) :
    ∃ N : SimplicialComplex ℝ D,
      N.faces.Finite ∧ N.IsSubdivision K ∧ ∀ i ∈ s, N.IsSubdivision (J i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨K, hK, SimplicialComplex.IsSubdivision.refl K, by simp⟩
  | @insert k s hks ih =>
    obtain ⟨N, hN, hNK, hNJ⟩ := ih
      (fun i hi => hJ i (Finset.mem_insert_of_mem hi))
      (fun i hi => hJK i (Finset.mem_insert_of_mem hi))
    have hk : k ∈ insert k s := Finset.mem_insert_self _ _
    obtain ⟨M, hM, hMN, hMk⟩ := N.exists_common_finite_subdivision (J k) hN (hJ k hk)
      (hNK.space_eq.trans (hJK k hk).space_eq.symm)
    refine ⟨M, hM, hMN.trans hNK, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hMk
    · exact hMN.trans (hNJ i hi)

theorem exists_simultaneous_normal_source_cofaces
    {D κ : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [Fintype κ]
    (K : SimplicialComplex ℝ D) (hK : K.faces.Finite)
    (f : κ → D → E) (hf : ∀ i, FinitePiecewiseAffineOn (f i) K.space)
    (r epsilon : κ → ℝ) (hepsilon : ∀ i, 0 < epsilon i) :
    ∃ (N : SimplicialComplex ℝ D) (c : κ → ℝ) (H : κ → E ≃ₜ E),
      N.faces.Finite ∧ N.IsSubdivision K ∧
      ∀ i, c i ∈ Ioo (0 : ℝ) (epsilon i) ∧
        (H i).toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid E ∧
        (∀ p, H i p = (p.1, p.2 + c i * normalMargin (r i) p)) ∧
        EqOn (H i) id (Metric.closedBall (0 : E) (r i))ᶜ ∧
        (∀ p, (H i p).1 = p.1) ∧ (∀ p, ((H i).symm p).1 = p.1) ∧
        N.AffineOnFaces ((normalGraphCoordinates (r i) (c i)) ∘ f i) ∧
        Disjoint (H i '' {p : E | p.2 = 0})
          (f i '' N.vertices ∩ {p : E | ‖p.1‖ < r i}) := by
  classical
  choose J hJ hJK hfamily using
    fun i => exists_normal_graph_source_refinement_family K hK (hf i) (r i)
  obtain ⟨N, hN, hNK, hNJ⟩ := exists_common_subdivision_of_finite_family K hK
    Finset.univ J (fun i _ => hJ i) (fun i _ => hJK i)
  have hmotions (i : κ) :=
    hfamily i N hN (hNJ i (Finset.mem_univ i)) (epsilon i) (hepsilon i)
  choose c H hc hPL hval hfix hfst hinv hfaces havoid using hmotions
  exact ⟨N, c, H, hN, hNK,
    fun i => ⟨hc i, hPL i, hval i, hfix i, hfst i, hinv i, hfaces i, havoid i⟩⟩

end PoincareConjecture.M76.CollarMesh
