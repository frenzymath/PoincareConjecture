import PoincareConjecture.Proofs.M76.Dehn.Mathlib.CoveringPullback
import PoincareConjecture.Proofs.M76.Mathlib.CoveringDeformationRetraction
import Mathlib.Topology.Homotopy.Path












set_option autoImplicit false

open Set unitInterval

namespace ContinuousMap.Homotopy




theorem connectedSpace_of_range {X : Type*} [TopologicalSpace X]
    {f : C(X, X)} (H : (ContinuousMap.id X).Homotopy f)
    (hf : IsConnected (range f)) : ConnectedSpace X := by
  obtain ⟨a, ha⟩ := hf.nonempty
  apply connectedSpace_iff_connectedComponent.mpr
  refine ⟨a, eq_univ_of_forall fun x => ?_⟩
  have hfa : f x ∈ connectedComponent a :=
    hf.subset_connectedComponent ha (mem_range_self x)
  have hxf : x ∈ connectedComponent (f x) :=
    pathComponent_subset_component (f x) ⟨(H.evalAt x).symm⟩
  rw [connectedComponent_eq hfa]
  exact hxf

end ContinuousMap.Homotopy

namespace IsCoveringMap

variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]






theorem connectedSpace_pullback_of_common_deformation
    {N A : Set X} (hAN : A ⊆ N)
    {r : C(X, X)} (H : (ContinuousMap.id X).HomotopyRel r A)
    (hr : ∀ x, r x ∈ A)
    {s : C(N, N)}
    (K : (ContinuousMap.id N).HomotopyRel s (Subtype.val ⁻¹' A))
    (hs : ∀ n, (s n : X) ∈ A)
    {p : E → N} (hp : IsCoveringMap p) [ConnectedSpace E] :
    ConnectedSpace (CoveringPullback.Total p (fun x => (⟨r x, hAN (hr x)⟩ : N))) := by
  let f : C(X, N) := ⟨fun x => ⟨r x, hAN (hr x)⟩, r.continuous.subtype_mk _⟩
  let Q := CoveringPullback.Total p f
  let q : Q → X := CoveringPullback.proj p f
  have hq : IsCoveringMap q := CoveringPullback.isCoveringMap hp f.continuous
  have hrfix (a : X) (ha : a ∈ A) : r a = a := by
    rw [← H.toHomotopy.apply_one a]
    exact H.eq_fst 1 ha
  let B : Set E := p ⁻¹' (Subtype.val ⁻¹' A)
  have hB : IsConnected B := hp.isConnected_preimage_of_deformation K hs
  let : ConnectedSpace B := isConnected_iff_connectedSpace.mp hB
  let j : B → Q := fun e =>
    ⟨((p e : X), e), Subtype.ext (hrfix (p e) e.2)⟩
  have hj : Continuous j :=
    ((continuous_subtype_val.comp (hp.continuous.comp continuous_subtype_val)).prodMk
      continuous_subtype_val).subtype_mk _
  have hjrange : range j = q ⁻¹' A := by
    ext z
    constructor
    · rintro ⟨e, rfl⟩
      exact e.2
    · intro hz
      have hpz : (p z.1.2 : X) = z.1.1 :=
        (congrArg Subtype.val z.2).symm.trans (hrfix z.1.1 hz)
      have heB : z.1.2 ∈ B := by
        change (p z.1.2 : X) ∈ A
        rw [hpz]
        exact hz
      refine ⟨⟨z.1.2, heB⟩, ?_⟩
      apply Subtype.ext
      exact Prod.ext hpz rfl
  have hqA : IsConnected (q ⁻¹' A) := hjrange ▸ isConnected_range hj
  obtain ⟨g, L, _, hg⟩ := hq.exists_relative_deformation_lift H hr
  exact L.toHomotopy.connectedSpace_of_range (hg.symm ▸ hqA)






theorem exists_two_sheet_pullback_of_common_deformation
    {N A : Set X} (hAN : A ⊆ N)
    {r : C(X, X)} (H : (ContinuousMap.id X).HomotopyRel r A)
    (hr : ∀ x, r x ∈ A)
    {s : C(N, N)}
    (K : (ContinuousMap.id N).HomotopyRel s (Subtype.val ⁻¹' A))
    (hs : ∀ n, (s n : X) ∈ A)
    {p : E → N} (hp : IsCoveringMap p) [ConnectedSpace E]
    (hcard : ∀ n : N, (p ⁻¹' {n}).ncard = 2) :
    let f : X → N := fun x => ⟨r x, hAN (hr x)⟩
    IsCoveringMap (CoveringPullback.proj p f) ∧
      ConnectedSpace (CoveringPullback.Total p f) ∧
      ∀ x : X, (CoveringPullback.proj p f ⁻¹' {x}).ncard = 2 := by
  dsimp only
  refine ⟨CoveringPullback.isCoveringMap hp (r.continuous.subtype_mk _),
    hp.connectedSpace_pullback_of_common_deformation hAN H hr K hs, ?_⟩
  intro x
  rw [CoveringPullback.fiber_ncard]
  exact hcard _

end IsCoveringMap
