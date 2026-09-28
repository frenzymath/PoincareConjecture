import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Tubes.PairCoordinates

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

theorem exists_restricted_whole_pair_coordinates
    {E F X ι : Type*} [TopologicalSpace E] [TopologicalSpace F]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    {f : E → X} {g : F → X} {S T : Set E} {U V : Set F} {R : Set X}
    (hS : IsCompact S) (hU : IsCompact U) (hTS : T ⊆ S) (hVU : V ⊆ U)
    (hf : ContinuousOn f S) (hg : ContinuousOn g U)
    (hfi : InjOn f S) (hgi : InjOn g U)
    {x : E} {y : F} (hx : x ∈ interior T) (hy : y ∈ interior V)
    (hxy : f x = g y) (hxR : f x ∈ interior R)
    (C : OriginalSurfacePairChart e (f '' S) (g '' U) (f x) false) :
    ∃ Q : OpenPartialHomeomorph X (Fin 3 → ℝ), f x ∈ Q.source ∧ Q.source ⊆ interior R ∧
      (∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid (Fin 3 → ℝ)) ∧
      (∀ z ∈ Q.source, z ∈ f '' T ↔ Q z 0 = 0) ∧
      (∀ z ∈ Q.source, z ∈ g '' V ↔ Q z 1 = 0) := by
  let A := f '' (S \ interior T)
  let B := g '' (U \ interior V)
  have hA : IsClosed A :=
    ((hS.diff isOpen_interior).image_of_continuousOn (hf.mono sdiff_subset)).isClosed
  have hB : IsClosed B :=
    ((hU.diff isOpen_interior).image_of_continuousOn (hg.mono sdiff_subset)).isClosed
  have hxA : f x ∉ A := by
    rintro ⟨z,hz,hzx⟩
    exact hz.2 ((hfi (hTS (interior_subset hx)) hz.1 hzx.symm) ▸ hx)
  have hxB : f x ∉ B := by
    rintro ⟨z,hz,hzx⟩
    exact hz.2 ((hgi (hVU (interior_subset hy)) hz.1 (hxy.symm.trans hzx.symm)) ▸ hy)
  obtain ⟨Q,hxQ,hQW,hQ,hfirst,hsecond⟩ := exists_whole_pair_coordinates C
    ((interior R \ A) \ B) ((isOpen_interior.sdiff hA).sdiff hB) ⟨⟨hxR,hxA⟩,hxB⟩
  refine ⟨Q,hxQ,fun _ hz => (hQW hz).1.1,hQ,?_,?_⟩
  · intro z hz
    rw [← hfirst z hz]
    constructor
    · exact fun h => image_mono hTS h
    · rintro ⟨a,ha,rfl⟩
      have hai : a ∈ interior T := by
        by_contra hh
        exact (hQW hz).1.2 ⟨a,⟨ha,hh⟩,rfl⟩
      exact ⟨a,interior_subset hai,rfl⟩
  · intro z hz
    rw [← hsecond z hz]
    constructor
    · exact fun h => image_mono hVU h
    · rintro ⟨a,ha,rfl⟩
      have hai : a ∈ interior V := by
        by_contra hh
        exact (hQW hz).2 ⟨a,⟨ha,hh⟩,rfl⟩
      exact ⟨a,interior_subset hai,rfl⟩

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
