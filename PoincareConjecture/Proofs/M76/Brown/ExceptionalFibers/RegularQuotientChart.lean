import PoincareConjecture.Proofs.M76.Brown.ExceptionalFibers.RegularQuotient
import Mathlib.Topology.OpenPartialHomeomorph.Constructions










set_option autoImplicit false

open Set Topology

namespace Homeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]




theorem exists_ambient_chart {U : Set X} {V : Set Y} (R : U ≃ₜ V)
    (hU : IsOpen U) (hV : IsOpen V) (hne : U.Nonempty) :
    ∃ e : OpenPartialHomeomorph X Y, e.source = U ∧ e.target = V ∧
      ∀ x : U, e x = (R x : Y) := by
  obtain ⟨x, hx⟩ := hne
  let : Nonempty U := ⟨⟨x, hx⟩⟩
  let : Nonempty Y := ⟨(R ⟨x, hx⟩ : Y)⟩
  let f : U → Y := Subtype.val ∘ R
  have hf : IsOpenEmbedding f := hV.isOpenEmbedding_subtypeVal.comp R.isOpenEmbedding
  let a := hf.toOpenPartialHomeomorph f
  let e := a.lift_openEmbedding hU.isOpenEmbedding_subtypeVal
  refine ⟨e, ?_, ?_, ?_⟩
  · change Subtype.val '' a.source = U
    rw [IsOpenEmbedding.toOpenPartialHomeomorph_source, image_univ, Subtype.range_val]
  · change a.target = V
    rw [IsOpenEmbedding.toOpenPartialHomeomorph_target]
    change range (Subtype.val ∘ R) = V
    rw [range_comp, R.surjective.range_eq, image_univ, Subtype.range_val]
  · intro z
    exact a.lift_openEmbedding_apply hU.isOpenEmbedding_subtypeVal

end Homeomorph

namespace Topology.IsQuotientMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]




theorem exists_regular_chart {q : X → Y} (hq : IsQuotientMap q)
    {T : Set Y} (hT : IsOpen T) (hne : T.Nonempty) (hinj : InjOn q (q ⁻¹' T)) :
    ∃ e : OpenPartialHomeomorph X Y, e.source = q ⁻¹' T ∧ e.target = T ∧
      EqOn e q (q ⁻¹' T) := by
  obtain ⟨R, hR⟩ := hq.exists_regular_homeomorph hT hinj
  have hpre : (q ⁻¹' T).Nonempty := by
    obtain ⟨y, hy⟩ := hne
    obtain ⟨x, hx⟩ := hq.surjective y
    refine ⟨x, ?_⟩
    change q x ∈ T
    rw [hx]
    exact hy
  obtain ⟨e, hes, het, he⟩ := R.exists_ambient_chart (hT.preimage hq.continuous) hT hpre
  refine ⟨e, hes, het, ?_⟩
  intro x hx
  exact (he ⟨x, hx⟩).trans (hR ⟨x, hx⟩)

end Topology.IsQuotientMap
