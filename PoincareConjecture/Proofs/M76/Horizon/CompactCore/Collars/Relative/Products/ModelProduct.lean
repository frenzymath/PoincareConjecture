import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Products.VertexProductConstruction
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricNeighborhoodCarrier

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

local notation "I" => Icc (-1 : ℝ) 1

open Classical in

theorem CoorientedSurfaceStars.vertex_bases_cover
    (T : CoorientedSurfaceStars E) :
    (⋃ p : (T.marked 2).vertices, T.surfaceBase {(p : E)}) =
      (T.marked 2).space := by
  classical
  let : Fintype (T.marked 2).faces := (T.marked_finite 2).fintype
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp⟩ := mem_iUnion.mp hx
    exact hp.2
  · intro hx
    have hxn := (T.marked 2).space_subset_barycentricNeighborhood
      (show T.marked 2 ≤ T.marked 2 from le_rfl) hx
    rw [(T.marked 2).barycentricNeighborhood_space_eq_iUnion_dualBlocks] at hxn
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hxn
    refine mem_iUnion.mpr ⟨⟨p, hp⟩, ?_⟩
    exact (T.dualRegion_inter_surface {p}).symm.subset hxp

open Classical in

theorem SurfaceVertexProducts.exists_model_product
    {T : CoorientedSurfaceStars E} (P : SurfaceVertexProducts T) :
    ∃ g : E × ℝ → E,
      FinitePiecewiseAffineOn g ((T.marked 2).space ×ˢ I) ∧
      InjOn g ((T.marked 2).space ×ˢ I) ∧
      g '' ((T.marked 2).space ×ˢ I) =
        ⋃ p : (T.marked 2).vertices, T.dualRegion {(p : E)} ∧
      (∀ x ∈ (T.marked 2).space, g (x, 0) = x) ∧
      (∀ x ∈ (T.marked 2).space ×ˢ I,
        g x ∈ (T.marked 1).space ↔ x.1 ∈ (T.marked 1).space) ∧
      (∀ (p : (T.marked 2).vertices) x, x ∈ (T.marked 2).space ×ˢ I →
        g x ∈ (T.ambient.closedStar p).space → (0 ≤ T.height p (g x) ↔ 0 ≤ x.2)) ∧
      ∀ (p : (T.marked 2).vertices) x, x ∈ (T.marked 2).space ×ˢ I →
        g x ∈ (T.ambient.closedStar p).space → (T.height p (g x) ≤ 0 ↔ x.2 ≤ 0) := by
  classical
  let : Finite (T.marked 2).vertices :=
    ((T.marked 2).finite_vertices_of_finite_faces (T.marked_finite 2)).to_subtype
  let S : (T.marked 2).vertices → Set (E × ℝ) := fun p => T.surfaceBase {(p : E)} ×ˢ I
  have hcover : (⋃ p, S p) = (T.marked 2).space ×ˢ I := by
    ext x
    constructor
    · intro hx
      obtain ⟨p, hp⟩ := mem_iUnion.mp hx
      exact ⟨T.vertex_bases_cover.subset (mem_iUnion.mpr ⟨p, hp.1⟩), hp.2⟩
    · rintro ⟨hx, ht⟩
      obtain ⟨p, hp⟩ := mem_iUnion.mp (T.vertex_bases_cover.symm.subset hx)
      exact mem_iUnion.mpr ⟨p, hp, ht⟩
  let g : E × ℝ → E := fun x => if hx : x ∈ ⋃ p, S p then
    P.map (mem_iUnion.mp hx).choose x else 0
  have hvalue (p : (T.marked 2).vertices) (x : E × ℝ) (hx : x ∈ S p) :
      g x = P.map p x := by
    have hu : x ∈ ⋃ q, S q := mem_iUnion.mpr ⟨p, hx⟩
    dsimp only [g]
    rw [dif_pos hu]
    exact P.agrees _ p x ⟨⟨(mem_iUnion.mp hu).choose_spec.1, hx.1⟩, hx.2⟩
  have hPL : FinitePiecewiseAffineOn g ((T.marked 2).space ×ˢ I) := by
    rw [← hcover]
    exact FinitePiecewiseAffineOn.iUnion fun p =>
      (P.piecewiseAffine p).congr fun x hx => (hvalue p x hx).symm
  have htarget (p : (T.marked 2).vertices) (x : E × ℝ) (hx : x ∈ S p) :
      P.map p x ∈ T.dualRegion {(p : E)} :=
    (P.image_eq p).subset ⟨x, hx, rfl⟩
  have hinj : InjOn g ((T.marked 2).space ×ˢ I) := by
    intro x hx y hy hxy
    obtain ⟨p, hxp⟩ := mem_iUnion.mp (hcover.symm.subset hx)
    obtain ⟨q, hyq⟩ := mem_iUnion.mp (hcover.symm.subset hy)
    have hmaps : P.map p x = P.map q y :=
      (hvalue p x hxp).symm.trans (hxy.trans (hvalue q y hyq))
    have hint : P.map p x ∈ T.dualRegion {(p : E)} ∩ T.dualRegion {(q : E)} :=
      ⟨htarget p x hxp, hmaps.symm ▸ htarget q y hyq⟩
    obtain ⟨z, hz, hzx⟩ := (P.overlap_image p q).symm.subset hint
    have hzx' : z = x := P.injective p ⟨hz.1.1, hz.2⟩ hxp hzx
    subst z
    exact P.injective q ⟨hz.1.2, hz.2⟩ hyq ((P.agrees p q x hz).symm.trans hmaps)
  refine ⟨g, hPL, hinj, ?_, ?_, ?_, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨p, hp⟩ := mem_iUnion.mp (hcover.symm.subset hx)
      rw [hvalue p x hp]
      exact mem_iUnion.mpr ⟨p, htarget p x hp⟩
    · intro hy
      obtain ⟨p, hp⟩ := mem_iUnion.mp hy
      obtain ⟨x, hx, hxy⟩ := (P.image_eq p).symm.subset hp
      exact ⟨x, hcover.subset (mem_iUnion.mpr ⟨p, hx⟩), (hvalue p x hx).trans hxy⟩
  · intro x hx
    obtain ⟨p, hp⟩ := mem_iUnion.mp (T.vertex_bases_cover.symm.subset hx)
    exact (hvalue p (x, 0) ⟨hp, by norm_num⟩).trans (P.central p x hp)
  · intro x hx
    obtain ⟨p, hp⟩ := mem_iUnion.mp (hcover.symm.subset hx)
    rw [hvalue p x hp]
    exact P.proper p x hp

  · intro p x hx hp
    obtain ⟨q, hq⟩ := mem_iUnion.mp (hcover.symm.subset hx)
    have hxq : g x ∈ T.dualRegion {(q : E)} := (hvalue q x hq).symm ▸ htarget q x hq
    have hqstar := T.dualRegion_subset_star q (Finset.mem_singleton_self _) hxq
    exact (T.nonneg_agree p q (g x) hp hqstar).trans (by
      rw [hvalue q x hq]
      exact P.positive q x hq)
  · intro p x hx hp
    obtain ⟨q, hq⟩ := mem_iUnion.mp (hcover.symm.subset hx)
    have hxq : g x ∈ T.dualRegion {(q : E)} := (hvalue q x hq).symm ▸ htarget q x hq
    have hqstar := T.dualRegion_subset_star q (Finset.mem_singleton_self _) hxq
    exact (T.nonpos_agree p q hp hqstar).trans (by
      rw [hvalue q x hq]
      exact P.negative q x hq)

theorem CoorientedSurfaceStars.exists_model_product (T : CoorientedSurfaceStars E) :
    ∃ g : E × ℝ → E,
      FinitePiecewiseAffineOn g ((T.marked 2).space ×ˢ I) ∧
      InjOn g ((T.marked 2).space ×ˢ I) ∧
      g '' ((T.marked 2).space ×ˢ I) =
        ⋃ p : (T.marked 2).vertices, T.dualRegion {(p : E)} ∧
      (∀ x ∈ (T.marked 2).space, g (x, 0) = x) ∧
      (∀ x ∈ (T.marked 2).space ×ˢ I,
        g x ∈ (T.marked 1).space ↔ x.1 ∈ (T.marked 1).space) ∧
      (∀ (p : (T.marked 2).vertices) x, x ∈ (T.marked 2).space ×ˢ I →
        g x ∈ (T.ambient.closedStar p).space → (0 ≤ T.height p (g x) ↔ 0 ≤ x.2)) ∧
      ∀ (p : (T.marked 2).vertices) x, x ∈ (T.marked 2).space ×ˢ I →
        g x ∈ (T.ambient.closedStar p).space → (T.height p (g x) ≤ 0 ↔ x.2 ≤ 0) := by
  obtain ⟨P⟩ := T.exists_vertex_products
  exact P.exists_model_product

end Geometry.SimplicialComplex
