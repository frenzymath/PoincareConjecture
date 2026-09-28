import PoincareConjecture.Proofs.M76.Wall.OriginalRelativeHeightChart
import PoincareConjecture.Proofs.M76.Wall.OriginalHeightRegion
import PoincareConjecture.Proofs.M76.Wall.Mathlib.OriginalUnionCornerCharts
import PoincareConjecture.Proofs.M76.Wall.Mathlib.ExteriorHalfspaceChart

set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76

open Classical in

theorem exists_original_exterior_height_corner
    {E V X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V)
    (K N D : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hNK : N ≤ K) (hDK : D ≤ K)
    {C L W : Set X} (hL : IsClosed L) (hLC : L ⊆ C)
    (H : C ≃ₜ K.space) (g : E → C) (hgc : ContinuousOn g K.space)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (F : X → E) (hHF : ∀ y : C, (H y : E) = F y)
    (hN : N.space = F '' (C \ interior L)) (hD : D.space = F '' frontier L)
    (A : Set E) {f : E → ℝ} (hf : K.AffineOnFaces f)
    (hzero : ∀ v ∈ K.vertices, v ∉ A → f v = 0)
    (hstars : ∀ p ∈ K.vertices, p ∈ A →
      ∃ G : OpenPartialHomeomorph X V,
        MapsTo (fun z => (g z : X)) (K.closedStar p).space G.source ∧
        (K.closedStar p).AffineOnFaces (fun z => G (g z)) ∧
        (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V) ∧
        G.source ⊆ interior C ∩ W ∧
        (G.source ⊆ Lᶜ ∨ ∃ (psi : V →ᴬ[ℝ] ℝ) (u : V),
          psi.contLinear u = 1 ∧
          (∀ y ∈ G.source, y ∈ L ↔ 0 ≤ psi (G y)) ∧
          ∀ y ∈ G.source, y ∈ frontier L ↔ psi (G y) = 0))
    (x : K.space) (hxD : (x : E) ∈ D.space) (hpos : 0 < f x)
    (hreg : ∀ v ∈ K.vertices, f v ≠ f x) :
    let R := (fun z => (g z : X)) '' (N.space ∩ {z | f x ≤ f z})
    ∃ (a : V →ᴬ[ℝ] ℝ) (u : V) (P U : OpenPartialHomeomorph X V),
      a.contLinear u = 1 ∧ (-a).contLinear (-u) = 1 ∧
      (g x : X) ∈ P.source ∧ (g x : X) ∈ U.source ∧
      (-a) (P (g x)) = 0 ∧ a (U (g x)) = 0 ∧
      P.source = U.source ∧ P.source ⊆ interior C ∩ W ∧
      (∀ i, (e i).symm.trans P ∈ piecewiseAffineGroupoid V) ∧
      (∀ i, (e i).symm.trans U ∈ piecewiseAffineGroupoid V) ∧
      (∀ y ∈ P.source, y ∈ R ↔ 0 ≤ (-a) (P y)) ∧
      (∀ y ∈ U.source, y ∈ L ∪ R ↔ 0 ≤ a (U y)) ∧
      (∀ y ∈ P.source, y ∈ frontier R ↔
        (y ∈ frontier L ∧ f x ≤ f (F y)) ∨
          (y ∈ C \ interior L ∧ f (F y) = f x)) ∧
      ∀ y ∈ U.source, y ∈ frontier (L ∪ R) ↔
        (y ∈ frontier L ∧ f (F y) ≤ f x) ∨
          (y ∈ C \ interior L ∧ f (F y) = f x) := by
  classical
  let R := (fun z => (g z : X)) '' (N.space ∩ {z | f x ≤ f z})
  have hsupport : ∀ p ∈ K.vertices, p ∈ A →
      MapsTo (fun z => (g z : X)) (K.closedStar p).space (interior C ∩ W) := by
    intro p hpK hpA
    obtain ⟨G, hsource, _, _, hinside, _⟩ := hstars p hpK hpA
    exact fun z hz => hinside (hsource hz)
  obtain ⟨_, _, hR, _⟩ := original_exterior_height_region K N hK hNK hL hLC
    H g hgc hg F hHF hN A hf hzero hsupport hpos
  obtain ⟨a, b, u, w, Q, hau, hbw, haw, hxQ, haQ, hbQ, hsource,
    hQ, hheight, hhalf, hfrontL⟩ := exists_original_relative_height_chart
      e K D hK hDK hL hLC H g hg F hHF hD A hf hzero hstars x hxD hpos.ne' hreg
  have hane : a.toAffineMap.linear ≠ 0 := by
    intro heq
    have hval : a.toAffineMap.linear u = 1 := hau
    rw [heq] at hval
    norm_num at hval
  have hanu : (-a).contLinear (-u) = 1 := by
    change -a.contLinear (-u) = 1
    rw [map_neg, neg_neg, hau]
  have hanne : (-a).toAffineMap.linear ≠ 0 := by
    change -a.toAffineMap.linear ≠ 0
    exact neg_ne_zero.mpr hane
  have hext := (Q.exterior_halfspace_and_frontier
    (fun y hy => (hsource hy).1) a hane hhalf).1
  have hquadrant : ∀ y ∈ Q.source, y ∈ R ↔ a (Q y) ≤ 0 ∧ 0 ≤ b (Q y) := by
    intro y hy
    change y ∈ (fun z => (g z : X)) '' (N.space ∩ {z | f x ≤ f z}) ↔ _
    rw [hR]
    change (y ∈ C \ interior L ∧ f x ≤ f (F y)) ↔ _
    rw [hext y hy, hheight y hy]
    simp only [ContinuousAffineMap.neg_apply, neg_nonneg, sub_nonneg]
  obtain ⟨P, U, hPs, hUs, hP, hU, hPhalf, hUhalf, hPfront, hUfront⟩ :=
    Q.exists_original_union_corner_charts e hQ a b u w hau hbw haw hhalf hquadrant
  have hxP : (g x : X) ∈ P.source := hPs.symm.subset hxQ
  have hxU : (g x : X) ∈ U.source := hUs.symm.subset hxQ
  have hxR : (g x : X) ∈ frontier R :=
    (hPfront _ hxQ).mpr (Or.inl ⟨haQ, by rw [hbQ]⟩)
  have hxLR : (g x : X) ∈ frontier (L ∪ R) :=
    (hUfront _ hxQ).mpr (Or.inl ⟨haQ, by rw [hbQ]⟩)
  have hPzero : (-a) (P (g x)) = 0 :=
    ((P.isImage_frontier_of_affine_nonneg (-a) hanne hPhalf).apply_mem_iff hxP).mpr hxR
  have hUzero : a (U (g x)) = 0 :=
    ((U.isImage_frontier_of_affine_nonneg a hane hUhalf).apply_mem_iff hxU).mpr hxLR
  refine ⟨a, u, P, U, hau, hanu, hxP, hxU, hPzero, hUzero,
    hPs.trans hUs.symm, (fun y hy => hsource (hPs.subset hy)),
    hP, hU, hPhalf, hUhalf, ?_, ?_⟩
  · intro y hy
    have hyQ : y ∈ Q.source := hPs.subset hy
    rw [hPfront y hyQ, hfrontL y hyQ, hext y hyQ, hheight y hyQ]
    simp only [ContinuousAffineMap.neg_apply, neg_nonneg, sub_nonneg, sub_eq_zero]
    tauto
  · intro y hy
    have hyQ : y ∈ Q.source := hUs.subset hy
    rw [hUfront y hyQ, hfrontL y hyQ, hext y hyQ, hheight y hyQ]
    simp only [ContinuousAffineMap.neg_apply, neg_nonneg, sub_nonpos, sub_eq_zero]
    tauto

end PoincareConjecture.M76
