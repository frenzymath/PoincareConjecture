import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.Topology.Compactness.Lindelof










set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture.M60




theorem ae_imp_of_locally_ae {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) {S : Set X} (hS : IsLindelof S) {p : X → Prop}
    (hlocal : ∀ x ∈ S, ∃ U ∈ 𝓝 x, ∀ᵐ y ∂μ, y ∈ U → p y) :
    ∀ᵐ y ∂μ, y ∈ S → p y := by
  classical
  choose U hU hp using hlocal
  obtain ⟨T, hT, hcover⟩ := hS.elim_nhds_subcover' U hU
  have hall : ∀ᵐ y ∂μ, ∀ x ∈ T, y ∈ U (x : S) x.property → p y :=
    (ae_ball_iff hT).mpr (fun x _ => hp (x : S) x.property)
  filter_upwards [hall] with y hy hys
  obtain ⟨x, hx⟩ := mem_iUnion.mp (hcover hys)
  obtain ⟨hxT, hyU⟩ := mem_iUnion.mp hx
  exact hy x hxT hyU




theorem aestronglyMeasurable_restrict_of_locally
    {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [TopologicalSpace Y] [TopologicalSpace.PseudoMetrizableSpace Y]
    (μ : Measure X) {S : Set X} (hS : IsLindelof S) {f : X → Y}
    (hlocal : ∀ x ∈ S, ∃ U ∈ 𝓝 x, AEStronglyMeasurable f (μ.restrict U)) :
    AEStronglyMeasurable f (μ.restrict S) := by
  classical
  choose U hU hm using hlocal
  obtain ⟨T, hT, hcover⟩ := hS.elim_nhds_subcover' U hU
  let : Countable T := hT.to_subtype
  have hsub : S ⊆ ⋃ x : T, U x.val x.val.property := by
    intro y hy
    obtain ⟨x, hx⟩ := mem_iUnion.mp (hcover hy)
    obtain ⟨hxT, hyU⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨⟨x, hxT⟩, hyU⟩
  have hall : AEStronglyMeasurable f (μ.restrict (⋃ x : T, U x.val x.val.property)) :=
    AEStronglyMeasurable.iUnion (fun x : T => hm x.val x.val.property)
  exact hall.mono_measure (Measure.restrict_mono hsub le_rfl)

end PoincareConjecture.M60
