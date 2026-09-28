import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Data.Fintype.Perm










set_option autoImplicit false

namespace IsCoveringMap

set_option backward.isDefEq.respectTransparency.types false in
theorem nontrivial_fundamentalGroup_of_finite_fiber
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (hp : IsCoveringMap p) (e : E)
    [Finite (p ⁻¹' {p e})] [Infinite (FundamentalGroup X (p e))] :
    Nontrivial (FundamentalGroup E e) := by
  classical
  by_contra h
  let : Subsingleton (FundamentalGroup E e) := not_nontrivial_iff_subsingleton.mp h
  have hinj : Function.Injective (hp.monodromyPerm (p e)) := by
    apply (injective_iff_map_eq_one (hp.monodromyPerm (p e))).mpr
    intro gamma hgamma
    have hfix : hp.monodromy gamma ⟨e, rfl⟩ = ⟨e, rfl⟩ := by
      exact congrArg (fun f : Equiv.Perm (p ⁻¹' {p e}) => f ⟨e, rfl⟩) hgamma
    let delta : FundamentalGroup E e :=
      (hp.liftPathQuotient gamma ⟨e, rfl⟩).cast rfl (congrArg Subtype.val hfix).symm
    have hmap : Path.Homotopic.Quotient.map delta ⟨p, hp.continuous⟩ = gamma := by
      simp only [delta, Path.Homotopic.Quotient.map_cast, hp.map_liftPathQuotient,
        Path.Homotopic.Quotient.cast_cast, Path.Homotopic.Quotient.cast_rfl_rfl]
    have hdelta : delta = 1 := Subsingleton.elim _ _
    have hh := congrArg (FundamentalGroup.map ⟨p, hp.continuous⟩ e) hdelta
    change Path.Homotopic.Quotient.map delta ⟨p, hp.continuous⟩ = _ at hh
    simpa only [hmap, map_one] using hh
  exact (Finite.of_injective (hp.monodromyPerm (p e)) hinj).false

theorem nontrivial_fundamentalGroup_of_compact
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [CompactSpace E] [T1Space X]
    {p : E → X} (hp : IsCoveringMap p) (e : E)
    [Infinite (FundamentalGroup X (p e))] :
    Nontrivial (FundamentalGroup E e) := by
  let : CompactSpace (p ⁻¹' {p e}) :=
    isCompact_iff_compactSpace.mp (isClosed_singleton.preimage hp.continuous).isCompact
  let : DiscreteTopology (p ⁻¹' {p e}) := (hp (p e)).discreteTopology_fiber
  let : Finite (p ⁻¹' {p e}) := finite_of_compact_of_discrete
  exact hp.nontrivial_fundamentalGroup_of_finite_fiber e

end IsCoveringMap
