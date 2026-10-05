import PoincareLib.Topology.Manifold.NeckCap.Theory
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-!
# Product charts on full open preimages

Compactness removes all points outside a chart after shrinking around a
base point whose entire fiber is already in that chart. This is the
compact-complement step of Morgan--Tian A.20, p. 508; see the reviewed
full-preimage-restriction plan in the M25 case-fibration records.
-/

set_option autoImplicit false
open Set
open scoped Manifold ContDiff Topology
universe u
namespace PoincareMT.M25

/-- A product chart containing one entire fiber restricts to a product
chart on a full open preimage. MT A.20, p. 508, intrinsic producer GP4. -/
theorem exists_full_preimage_product_restriction
    {M : Type u} [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    (projection : M → UnitCircle) (hp : Continuous projection)
    (j : OpenPartialHomeomorph M (UnitTwoSphere × UnitCircle))
    (W : Set UnitCircle) (hW : IsOpen W)
    (htarget : j.target = univ ×ˢ W)
    (hs : ContMDiffOn (𝓡 3) ((𝓡 2).prod (𝓡 1)) ∞ j j.source)
    (hi : ContMDiffOn ((𝓡 2).prod (𝓡 1)) (𝓡 3) ∞ j.symm j.target)
    (hsecond : ∀ x ∈ j.source, (j x).2 = projection x)
    {b : UnitCircle} (hb : b ∈ W)
    (hfiber : projection ⁻¹' {b} ⊆ j.source) :
    ∃ V : Set UnitCircle, IsOpen V ∧ b ∈ V ∧ V ⊆ W ∧
      ∃ T : OpenPartialHomeomorph M (UnitTwoSphere × UnitCircle),
        T.source = projection ⁻¹' V ∧ T.target = univ ×ˢ V ∧
        ContMDiffOn (𝓡 3) ((𝓡 2).prod (𝓡 1)) ∞ T T.source ∧
        ContMDiffOn ((𝓡 2).prod (𝓡 1)) (𝓡 3) ∞ T.symm T.target ∧
        ∀ x ∈ T.source, (T x).2 = projection x := by
  let B : Set UnitCircle := projection '' j.sourceᶜ
  have hB : IsClosed B :=
    (j.open_source.isClosed_compl.isCompact.image hp).isClosed
  let V : Set UnitCircle := W \ B
  have hV : IsOpen V := hW.inter hB.isOpen_compl
  have hbV : b ∈ V := by
    refine ⟨hb, ?_⟩
    rintro ⟨x, hx, hxb⟩
    exact hx (hfiber hxb)
  have hVW : V ⊆ W := sdiff_subset
  have hpre : projection ⁻¹' V ⊆ j.source := by
    intro x hx
    by_contra hout
    exact hx.2 ⟨x, hout, rfl⟩
  have hinverse (y : UnitTwoSphere × UnitCircle) (hy : y ∈ j.target) :
      projection (j.symm y) = y.2 :=
    (hsecond _ (j.map_target hy)).symm.trans (congrArg Prod.snd (j.right_inv hy))
  let T := j.restrOpen (projection ⁻¹' V) (hV.preimage hp)
  have hsource : T.source = projection ⁻¹' V := by
    exact inter_eq_right.mpr hpre
  have hTtarget : T.target = univ ×ˢ V := by
    ext y
    change (y ∈ j.target ∧ projection (j.symm y) ∈ V) ↔
      (y.1 ∈ univ ∧ y.2 ∈ V)
    constructor
    · rintro ⟨hy, hpV⟩
      exact ⟨mem_univ _, hinverse y hy ▸ hpV⟩
    · rintro ⟨_, hyV⟩
      have hy : y ∈ j.target := htarget.symm ▸ ⟨mem_univ _, hVW hyV⟩
      exact ⟨hy, (hinverse y hy).symm ▸ hyV⟩
  refine ⟨V, hV, hbV, hVW, T, hsource, hTtarget, ?_, ?_, ?_⟩
  · exact hs.mono (fun _ hx => hx.1)
  · exact hi.mono (fun _ hy => hy.1)
  · intro x hx
    exact hsecond x hx.1

end PoincareMT.M25
