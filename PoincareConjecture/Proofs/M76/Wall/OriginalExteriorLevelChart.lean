import PoincareConjecture.Proofs.M76.Wall.OriginalSelectedHeightChart
import PoincareConjecture.Proofs.M76.Wall.OriginalHeightRegion
import PoincareConjecture.Proofs.M76.Wall.ProtectedPLIntersection
import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts

set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76

open Classical in

theorem exists_original_exterior_level_chart
    {E V X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V)
    (K N : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hNK : N ≤ K)
    {C L W : Set X} (hL : IsClosed L) (hLC : L ⊆ C)
    (H : C ≃ₜ K.space) (g : E → C) (hgc : ContinuousOn g K.space)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (F : X → E) (hHF : ∀ y : C, (H y : E) = F y)
    (hN : N.space = F '' (C \ interior L))
    (A : Set E) {f : E → ℝ} (hf : K.AffineOnFaces f)
    (hzero : ∀ v ∈ K.vertices, v ∉ A → f v = 0)
    (hstars : ∀ p ∈ K.vertices, p ∈ A →
      ∃ G : OpenPartialHomeomorph X V,
        MapsTo (fun z => (g z : X)) (K.closedStar p).space G.source ∧
        (K.closedStar p).AffineOnFaces (fun z => G (g z)) ∧
        (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V) ∧
        G.source ⊆ interior C ∩ W)
    (x : K.space) (hxL : (g x : X) ∉ L) (hpos : 0 < f x)
    (hreg : ∀ v ∈ K.vertices, f v ≠ f x) :
    let R := (fun z => (g z : X)) '' (N.space ∩ {z | f x ≤ f z})
    ∃ (b : V →ᴬ[ℝ] ℝ) (w : V) (P : OpenPartialHomeomorph X V),
      b.contLinear w = 1 ∧ (g x : X) ∈ P.source ∧ b (P (g x)) = 0 ∧
      P.source ⊆ (interior C ∩ W) ∩ Lᶜ ∧
      (∀ i, (e i).symm.trans P ∈ piecewiseAffineGroupoid V) ∧
      (∀ y ∈ P.source, y ∈ R ↔ 0 ≤ b (P y)) ∧
      (∀ y ∈ P.source, y ∈ L ∪ R ↔ 0 ≤ b (P y)) ∧
      (∀ y ∈ P.source, y ∈ frontier R ↔ f (F y) = f x) ∧
      ∀ y ∈ P.source, y ∈ frontier (L ∪ R) ↔ f (F y) = f x := by
  classical
  let R := (fun z => (g z : X)) '' (N.space ∩ {z | f x ≤ f z})
  have hsupport : ∀ p ∈ K.vertices, p ∈ A →
      MapsTo (fun z => (g z : X)) (K.closedStar p).space (interior C ∩ W) := by
    intro p hpK hpA
    obtain ⟨G, hsource, _, _, hinside⟩ := hstars p hpK hpA
    exact fun z hz => hinside (hsource hz)
  obtain ⟨_, _, hR, _⟩ := original_exterior_height_region K N hK hNK hL hLC
    H g hgc hg F hHF hN A hf hzero hsupport hpos
  obtain ⟨b, w, Q, hbw, hxQ, hbQ, hsource, _, hQ, hheight⟩ :=
    exists_original_selected_height_chart e K hK H g hg F hHF A hf hzero
      hstars x hpos.ne' hreg
  let P := Q.restrOpen Lᶜ hL.isOpen_compl
  have hPhalf : ∀ y ∈ P.source, y ∈ R ↔ 0 ≤ b (P y) := by
    intro y hy
    change y ∈ (fun z => (g z : X)) '' (N.space ∩ {z | f x ≤ f z}) ↔ _
    rw [hR]
    change (y ∈ C \ interior L ∧ f x ≤ f (F y)) ↔ 0 ≤ b (Q y)
    rw [hheight y hy.1, sub_nonneg]
    exact and_iff_right ⟨interior_subset (hsource hy.1).1,
      fun hyL => hy.2 (interior_subset hyL)⟩
  have hUhalf : ∀ y ∈ P.source, y ∈ L ∪ R ↔ 0 ≤ b (P y) := by
    intro y hy
    rw [mem_union]
    exact (or_iff_right hy.2).trans (hPhalf y hy)
  have hbne : b.toAffineMap.linear ≠ 0 := by
    intro heq
    have hval : b.toAffineMap.linear w = 1 := hbw
    rw [heq] at hval
    norm_num at hval
  have hPfront := P.isImage_frontier_of_affine_nonneg b hbne hPhalf
  have hUfront := P.isImage_frontier_of_affine_nonneg b hbne hUhalf
  refine ⟨b, w, P, hbw, ⟨hxQ, hxL⟩, hbQ,
    (fun y hy => ⟨hsource hy.1, hy.2⟩), ?_, hPhalf, hUhalf, ?_, ?_⟩
  · intro i
    exact (e i).piecewiseAffine_compatible_restrOpen_right Q (hQ i) hL.isOpen_compl
  · intro y hy
    change y ∈ frontier R ↔ f (F y) = f x
    rw [← hPfront.apply_mem_iff hy]
    change b (Q y) = 0 ↔ f (F y) = f x
    rw [hheight y hy.1, sub_eq_zero]
  · intro y hy
    change y ∈ frontier (L ∪ R) ↔ f (F y) = f x
    rw [← hUfront.apply_mem_iff hy]
    change b (Q y) = 0 ↔ f (F y) = f x
    rw [hheight y hy.1, sub_eq_zero]

end PoincareConjecture.M76
