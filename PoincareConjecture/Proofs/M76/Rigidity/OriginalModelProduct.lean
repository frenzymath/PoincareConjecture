import PoincareConjecture.Proofs.M76.Rigidity.OriginalVertexProducts
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricNeighborhoodCarrier

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}

open Classical in

theorem OriginalProperDiskTriangulation.vertex_bases_cover
    (T : OriginalProperDiskTriangulation e R j) :
    (⋃ p : (T.marked 2).vertices, T.diskDualBase {(p : T.index → ℝ × V3)}) =
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
    exact (T.dualRegion_inter_disk {p}).symm.subset hxp

open Classical in

theorem OriginalVertexProducts.exists_model_product
    {T : OriginalProperDiskTriangulation e R j} (P : OriginalVertexProducts T) :
    ∃ g : (T.index → ℝ × V3) × ℝ → (T.index → ℝ × V3),
      FinitePiecewiseAffineOn g ((T.marked 2).space ×ˢ I) ∧
      InjOn g ((T.marked 2).space ×ˢ I) ∧
      g '' ((T.marked 2).space ×ˢ I) =
        ⋃ p : (T.marked 2).vertices, T.dualRegion {(p : T.index → ℝ × V3)} ∧
      (∀ x ∈ (T.marked 2).space, g (x, 0) = x) ∧
      ∀ x ∈ (T.marked 2).space ×ˢ I,
        g x ∈ (T.marked 1).space ↔ x.1 ∈ (T.marked 1).space := by
  classical
  let E := T.index → ℝ × V3
  let : Finite (T.marked 2).vertices :=
    ((T.marked 2).finite_vertices_of_finite_faces (T.marked_finite 2)).to_subtype
  let S : (T.marked 2).vertices → Set (E × ℝ) := fun p => T.diskDualBase {(p : E)} ×ˢ I
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
  refine ⟨g, hPL, hinj, ?_, ?_, ?_⟩
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

end PoincareConjecture.M76
