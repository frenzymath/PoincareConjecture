import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.PrismFiberInterpolation
import Mathlib.Topology.LocallyFinite



set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1

theorem exists_continuous_prism_interpolation
    {E ι : Type*} [TopologicalSpace E] [T2Space E] [Finite ι]
    {A B : ι → Set E} (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i)
    (hA : ∀ i, IsCompact (A i))
    (hagree : ∀ i j (x : E) (hi : x ∈ B i) (hj : x ∈ B j) (t : I),
      (prismFiberInterpolation (H i) ⟨x,hi⟩ t : E) = prismFiberInterpolation (H j) ⟨x,hj⟩ t) :
    ∃ L : C((⋃ i, B i) × I, (⋃ i, B i)),
      ∀ i (x : B i) (t : I), (L (⟨x,mem_iUnion.mpr ⟨i,x.property⟩⟩,t) : E) =
        prismFiberInterpolation (H i) x t := by
  classical
  let U := (⋃ i, B i : Set E)
  have hclosed (i : ι) : IsClosed (B i) := by
    let : CompactSpace (A i ×ˢ I : Set (E × ℝ)) :=
      isCompact_iff_compactSpace.mp ((hA i).prod isCompact_Icc)
    let : CompactSpace (B i) := (H i).compactSpace
    exact (isCompact_iff_compactSpace.mpr inferInstance).isClosed
  let pieces (i : ι) : Set (U × I) := {z | (z.1 : E) ∈ B i}
  let maps (i : ι) : C(pieces i,U) :=
    ⟨fun z => ⟨prismFiberInterpolation (H i) ⟨z.1.1,z.2⟩ z.1.2,
      mem_iUnion.mpr ⟨i,(prismFiberInterpolation (H i) ⟨z.1.1,z.2⟩ z.1.2).property⟩⟩,by
      apply Continuous.subtype_mk
      apply continuous_subtype_val.comp
      exact (continuous_prismFiberInterpolation (H i)).comp
        ((((continuous_subtype_val.comp continuous_fst).comp continuous_subtype_val).subtype_mk _).prodMk
          (continuous_snd.comp continuous_subtype_val))⟩
  have hmaps (i j : ι) (z : U × I) (hi : z ∈ pieces i) (hj : z ∈ pieces j) :
      maps i ⟨z,hi⟩ = maps j ⟨z,hj⟩ := Subtype.ext (hagree i j z.1 hi hj z.2)
  have hcover : ⋃ i, pieces i = univ := by
    apply iUnion_eq_univ_iff.mpr
    intro z
    change ∃ i, (z.1 : E) ∈ B i
    exact mem_iUnion.mp z.1.property
  let L := Set.liftCover pieces (fun i => maps i) hmaps hcover
  have hval (i : ι) (z : pieces i) : L z = maps i z := Set.liftCover_coe z
  have hL : Continuous L := by
    apply (locallyFinite_of_finite pieces).continuous hcover
    · intro i
      exact (hclosed i).preimage (continuous_subtype_val.comp continuous_fst)
    · intro i
      rw [continuousOn_iff_continuous_domRestrict]
      have he : (pieces i).domRestrict L = maps i := funext (hval i)
      rw [he]
      exact (maps i).continuous
  refine ⟨⟨L,hL⟩,?_⟩
  intro i x t
  exact congrArg Subtype.val (hval i ⟨(⟨x,mem_iUnion.mpr ⟨i,x.property⟩⟩,t),x.property⟩)

end PoincareConjecture.M76.PrismBelt
