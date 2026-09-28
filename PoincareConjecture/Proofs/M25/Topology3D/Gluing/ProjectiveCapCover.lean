import PoincareConjecture.Proofs.M25.Topology3D.Gluing.CapStandardEnd
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.ClosedModelCapData
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.ProjectiveCover













set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M25.Topology3D




theorem capModelEquivalence_exists_puncturedProjective_cover
    {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
    {U : Set M} (hU : IsOpen U)
    {kind : CapModelKind} {p : RealProjectiveThree}
    (R : CapModelEquivalence kind p U)
    (hkind : kind = CapModelKind.puncturedProjective) :
    Nonempty (PoincareConjecture.StandardPuncturedProjectiveCover M p U) := by
  let : TopologicalSpace R.model := R.model_topology
  let : ChartedSpace E3 R.model := R.model_charted
  let : IsManifold (𝓡 3) ∞ R.model := R.model_manifold
  have hmodel : Nonempty
      (PoincareConjecture.StandardPuncturedProjectiveCover R.model p univ) := by
    have h := R.standard_smooth
    split at h
    · simp_all only [reduceCtorEq]
    · exact h
  obtain ⟨P⟩ := hmodel
  let e : PartialDiffeomorph (𝓡 3) (𝓡 3) M R.model ∞ :=
    { toFun := R.forward
      invFun := R.inverse
      source := U
      target := univ
      map_source' := fun _ _ => mem_univ _
      map_target' := fun y _ => R.inverse_mem y
      left_inv' := R.left_inverse
      right_inv' := fun y _ => R.right_inverse y
      open_source := hU
      open_target := isOpen_univ
      contMDiffOn_toFun := R.forward_smooth
      contMDiffOn_invFun := R.inverse_smooth }
  have hinverse : Function.Injective R.inverse := by
    intro x y hxy
    exact (R.right_inverse x).symm.trans
      ((congrArg R.forward hxy).trans (R.right_inverse y))
  refine ⟨{
    cover := R.inverse ∘ P.cover
    image_eq := ?_
    fibers := ?_
    local_diffeomorph := ?_ }⟩
  · apply Subset.antisymm
    · rintro _ ⟨x, _, rfl⟩
      exact R.inverse_mem (P.cover x)
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := P.image_eq.symm.subset (mem_univ (R.forward y))
      refine ⟨x, hx, ?_⟩
      change R.inverse (P.cover x) = y
      rw [hxy, R.left_inverse y hy]
  · intro x y hx hy
    exact hinverse.eq_iff.trans (P.fibers x y hx hy)
  · intro x
    exact (P.local_diffeomorph x).comp (𝓡 3) M
      ⟨e.symm, mem_univ _, fun _ _ => rfl⟩




theorem closedModelCapData_exists_puncturedProjective_cover
    {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (C : ClosedModelCapData g)
    (hkind : C.model_kind = CapModelKind.puncturedProjective) :
    Nonempty (PoincareConjecture.StandardPuncturedProjectiveCover
      M C.puncture C.carrier) :=
  capModelEquivalence_exists_puncturedProjective_cover
    C.carrier_open C.model_equivalence hkind




theorem capCertificate_exists_puncturedProjective_cover
    {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (C : CapCertificate g)
    (hkind : C.model_kind = CapModelKind.puncturedProjective) :
    Nonempty (PoincareConjecture.StandardPuncturedProjectiveCover
      M C.puncture C.carrier) :=
  capModelEquivalence_exists_puncturedProjective_cover
    C.carrier_open C.model_equivalence hkind

end PoincareConjecture.M25.Topology3D
