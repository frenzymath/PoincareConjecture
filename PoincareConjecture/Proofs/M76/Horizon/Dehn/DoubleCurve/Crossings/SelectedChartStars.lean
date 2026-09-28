import PoincareConjecture.Proofs.M76.PrimeReduction.CompatibleChartStars
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffineInverse









set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn



theorem exists_selected_compatible_chart_stars
    {E V X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace X] [Finite κ]
    (e : ι → OpenPartialHomeomorph X V)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f : E → X} (hf : PolyhedralPLInCharts e f K.space)
    {A : Set X} (hA : IsClosed A)
    (G : ↥(K.space ∩ f ⁻¹' A) → OpenPartialHomeomorph X V)
    (hG : ∀ q i, (e i).symm.trans (G q) ∈ piecewiseAffineGroupoid V)
    (hpoint : ∀ q, f q ∈ (G q).source)
    (J : κ → SimplicialComplex ℝ E) (hJ : ∀ a, (J a).faces.Finite)
    (hJK : ∀ a, (J a).space ⊆ K.space) (a : κ)
    (hJa : (J a).space = K.space ∩ f ⁻¹' A) :
    ∃ (N : SimplicialComplex ℝ E) (L : κ → SimplicialComplex ℝ E),
      N.faces.Finite ∧ N.IsSubdivision K ∧
      (∀ j, L j ≤ N ∧ (L j).space = (J j).space ∧
        ∀ s ∈ N.faces, (∀ v ∈ s, v ∈ (L j).vertices) → s ∈ (L j).faces) ∧
      ∀ p ∈ (L a).vertices, ∃ q : ↥(K.space ∩ f ⁻¹' A),
        MapsTo f (N.closedStar p).space (G q).source ∧
        (N.closedStar p).AffineOnFaces (G q ∘ f) := by
  classical
  choose idx hidx using hcover
  let H (q : K.space) : OpenPartialHomeomorph X V :=
    if h : f q ∈ A then G ⟨q, q.property, h⟩
    else (e (idx (f q))).restrOpen Aᶜ hA.isOpen_compl
  have hH (q : K.space) (i : ι) : (e i).symm.trans (H q) ∈ piecewiseAffineGroupoid V := by
    dsimp only [H]
    split_ifs with h
    · exact hG _ i
    · apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
      exact ((mem_piecewiseAffineGroupoid_iff_forward _).mp (he i (idx (f q)))).mono
        ((e i).symm.trans ((e (idx (f q))).restrOpen Aᶜ hA.isOpen_compl)).open_source
        (fun _ hz ↦ ⟨hz.1, hz.2.1⟩)
  have hHp (q : K.space) : f q ∈ (H q).source := by
    dsimp only [H]
    split_ifs with h
    · exact hpoint _
    · exact ⟨hidx (f q), h⟩
  obtain ⟨N, L, hN, hNK, hL, hstars⟩ :=
    hf.exists_full_compatible_chart_stars K hK H hH hHp J hJ hJK
  refine ⟨N, L, hN, hNK, hL, ?_⟩
  intro p hp
  have hpN : p ∈ N.vertices := (hL a).1 hp
  have hpA : f p ∈ A := (hJa.subset ((hL a).2.1.subset ((L a).vertices_subset_space hp))).2
  have hpstar : p ∈ (N.closedStar p).space :=
    (N.closedStar p).vertices_subset_space ⟨hpN, by
      simpa only [Finset.pair_eq_singleton] using (show {p} ∈ N.faces from hpN)⟩
  obtain ⟨q, hmap, hface⟩ := hstars p hpN
  have hq : f q ∈ A := by
    by_contra hn
    have hpH := hmap hpstar
    dsimp only [H] at hpH
    rw [dif_neg hn] at hpH
    exact hpH.2 hpA
  refine ⟨⟨q, q.property, hq⟩, ?_⟩
  simpa only [H, dif_pos hq] using And.intro hmap hface

end PoincareConjecture.M76.Dehn
