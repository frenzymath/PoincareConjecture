import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskVertexProducts
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Mathlib.ConnectedComplexGraph

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] {R D : Set E} {b : D2 ≃ₜ D}

private theorem disk_vertex_blocks_cover (T : HamiltonProperDiskTriangulation R D b) :
    (⋃ p : T.disk.vertices, T.diskVertexBlock p) = D := by
  classical
  let : Fintype T.disk.faces := (T.finite.subset T.disk_le).fintype
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp⟩ := mem_iUnion.mp hx
    apply T.disk_space.subset
    apply T.disk.barycentricSubdivision_isSubdivision.space_eq.subset
    exact SimplicialComplex.space_subset_of_le (T.disk.barycentricDualBlock_le {(p : E)}) hp
  · intro hx
    have hxn := T.disk.space_subset_barycentricNeighborhood
      (show T.disk ≤ T.disk from le_rfl) (T.disk_space.symm.subset hx)
    rw [T.disk.barycentricNeighborhood_space_eq_iUnion_dualBlocks] at hxn
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hxn
    exact mem_iUnion.mpr ⟨⟨p, hp⟩, hxp⟩

private theorem exists_glued_vertex_product [FiniteDimensional ℝ E]
    {T : HamiltonProperDiskTriangulation R D b} (P : HamiltonProperDiskVertexProducts T) :
    ∃ g : E × ℝ → E, FinitePiecewiseAffineOn g (D ×ˢ I) ∧ InjOn g (D ×ˢ I) ∧
      MapsTo g (D ×ˢ I) R ∧ (∀ x ∈ D, g (x, 0) = x) ∧
      ∀ x ∈ D ×ˢ I, g x ∈ frontier R ↔ x.1 ∈ frontier R := by
  classical
  let : Finite T.disk.vertices :=
    (T.disk.finite_vertices_of_finite_faces (T.finite.subset T.disk_le)).to_subtype
  let S : T.disk.vertices → Set (E × ℝ) := fun p => T.diskVertexBlock p ×ˢ I
  have hcover : (⋃ p, S p) = D ×ˢ I := by
    ext x
    constructor
    · intro hx
      obtain ⟨p, hp⟩ := mem_iUnion.mp hx
      exact ⟨(disk_vertex_blocks_cover T).subset (mem_iUnion.mpr ⟨p, hp.1⟩), hp.2⟩
    · rintro ⟨hx, ht⟩
      obtain ⟨p, hp⟩ := mem_iUnion.mp ((disk_vertex_blocks_cover T).symm.subset hx)
      exact mem_iUnion.mpr ⟨p, hp, ht⟩
  let g : E × ℝ → E := fun x => if hx : x ∈ ⋃ p, S p then
    P.map (mem_iUnion.mp hx).choose x else 0
  have hvalue (p : T.disk.vertices) (x : E × ℝ) (hx : x ∈ S p) : g x = P.map p x := by
    have hu : x ∈ ⋃ q, S q := mem_iUnion.mpr ⟨p, hx⟩
    dsimp only [g]
    rw [dif_pos hu]
    exact P.agrees _ p x ⟨⟨(mem_iUnion.mp hu).choose_spec.1, hx.1⟩, hx.2⟩
  have hPL : FinitePiecewiseAffineOn g (D ×ˢ I) := by
    rw [← hcover]
    exact FinitePiecewiseAffineOn.iUnion fun p =>
      (P.piecewiseAffine p).congr fun x hx => (hvalue p x hx).symm
  have htarget (p : T.disk.vertices) (x : E × ℝ) (hx : x ∈ S p) :
      P.map p x ∈ T.dualRegion {(p : E)} :=
    (P.image_eq p).subset ⟨x, hx, rfl⟩
  have hinj : InjOn g (D ×ˢ I) := by
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
  · intro x hx
    obtain ⟨p, hp⟩ := mem_iUnion.mp (hcover.symm.subset hx)
    rw [hvalue p x hp]
    exact (htarget p x hp).2
  · intro x hx
    obtain ⟨p, hp⟩ := mem_iUnion.mp ((disk_vertex_blocks_cover T).symm.subset hx)
    exact (hvalue p (x, 0) ⟨hp, by norm_num⟩).trans (P.central p x hp)
  · intro x hx
    obtain ⟨p, hp⟩ := mem_iUnion.mp (hcover.symm.subset hx)
    rw [hvalue p x hp]
    exact P.proper p x hp

theorem HamiltonProperDiskVertexProducts.exists_unmarked_disk_product
    [FiniteDimensional ℝ E] {T : HamiltonProperDiskTriangulation R D b}
    (P : HamiltonProperDiskVertexProducts T) (hb : b.IsFinitePL)
    (hproper : ∀ x : D2, (b x : E) ∈ frontier R ↔ (x : V2) ∈ Q2) :
    Nonempty (HamiltonUnmarkedDiskProduct R b) := by
  obtain ⟨g, hg, hgi, hgm, hgc, hgp⟩ := exists_glued_vertex_product P
  obtain ⟨f, hf, hfb⟩ := hb
  have hfm : MapsTo f D2 D := by
    intro x hx
    rw [← hfb ⟨x, hx⟩]
    exact (b ⟨x, hx⟩).property
  have hfi : InjOn f D2 := by
    intro x hx y hy hxy
    have heq : b ⟨x, hx⟩ = b ⟨y, hy⟩ :=
      Subtype.ext ((hfb ⟨x, hx⟩).trans (hxy.trans (hfb ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (b.injective heq)
  have hid : FinitePiecewiseAffineOn (id : ℝ → ℝ) I := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKI, _⟩, _⟩, _⟩ :=
      isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num)
    exact ⟨K, hK, hKI, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)⟩
  let F : V2 × ℝ → E × ℝ := Prod.map f id
  have hF : MapsTo F (D2 ×ˢ I) (D ×ˢ I) := fun x hx => ⟨hfm hx.1, hx.2⟩
  refine ⟨{
    map := g ∘ F
    piecewiseAffine := hg.comp (hf.prodMap hid) hF
    injective := ?_
    inside := hgm.comp hF
    proper := ?_
    central := ?_ }⟩
  · intro x hx y hy hxy
    have hFxy : F x = F y := hgi (hF hx) (hF hy) hxy
    exact Prod.ext (hfi hx.1 hy.1 (congrArg (fun z : E × ℝ => z.1) hFxy))
      (congrArg (fun z : E × ℝ => z.2) hFxy)
  · intro x hx
    change g (F x) ∈ frontier R ↔ x.1 ∈ Q2
    rw [hgp (F x) (hF hx)]
    change f x.1 ∈ frontier R ↔ x.1 ∈ Q2
    rw [← hfb ⟨x.1, hx.1⟩]
    exact hproper ⟨x.1, hx.1⟩
  · intro x
    change g (f x, 0) = b x
    exact (hgc (f x) (hfm x.property)).trans (hfb x).symm

end PoincareConjecture.M76.HamiltonIndexOne
