import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SimplicialCocycleConnected
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.CompactTerminalCover
import PoincareConjecture.Proofs.M76.Mathlib.FiniteBarycentricCoordinates

set_option autoImplicit false

universe u v

open Set

namespace PreAbstractSimplicialComplex.ModTwoEdgeCocycle

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  {ι : Type v} [Fintype ι] {A : PreAbstractSimplicialComplex ι}

theorem isCoboundary_of_terminal_common_deformation
    (c : A.ModTwoEdgeCocycle) (hvertex : ∀ i : ι, {i} ∈ A.faces)
    {N D : Set X} (hDN : D ⊆ N)
    {r : C(X, X)} (H : (ContinuousMap.id X).HomotopyRel r D)
    (hr : ∀ x, r x ∈ D)
    {s : C(N, N)}
    (K : (ContinuousMap.id N).HomotopyRel s (Subtype.val ⁻¹' D))
    (hs : ∀ n, (s n : X) ∈ D)
    (B : A.barycentricSpace ≃ₜ N)
    (hterminal : ∀ (Y : Type (max u v)) [TopologicalSpace Y]
      [T2Space Y] [ConnectedSpace Y] (p : Y → X),
      IsCoveringMap p → (∀ x, (p ⁻¹' {x}).ncard = 2) → False) :
    c.IsCoboundary := by
  classical
  let f : C(X, N) := ⟨fun x => ⟨r x, hDN (hr x)⟩, r.continuous.subtype_mk _⟩
  have hfrange : range f = Subtype.val ⁻¹' D := by
    ext n
    constructor
    · rintro ⟨x, rfl⟩
      exact hr x
    · intro hn
      refine ⟨n, Subtype.ext ?_⟩
      change r n = (n : X)
      rw [← H.toHomotopy.apply_one (n : X)]
      exact H.eq_fst 1 hn
  have hsrange : range s = Subtype.val ⁻¹' D := by
    ext n
    constructor
    · rintro ⟨x, rfl⟩
      exact hs x
    · intro hn
      refine ⟨n, ?_⟩
      rw [← K.toHomotopy.apply_one n]
      exact K.eq_fst 1 hn
  let : ConnectedSpace N := K.toHomotopy.connectedSpace_of_range
    ((hsrange.trans hfrange.symm).symm ▸ isConnected_range f.continuous)
  let : ConnectedSpace A.barycentricSpace := B.connectedSpace_iff.mpr inferInstance
  by_contra hc
  let : ConnectedSpace c.bundle.TotalSpace := c.connectedSpace_of_not_isCoboundary hvertex hc
  let p : c.bundle.TotalSpace → N := fun q => B (c.bundle.proj q)
  have hp : IsCoveringMap p := c.isCoveringMap.homeomorph_comp B
  have htwo (n : N) : (p ⁻¹' {n}).ncard = 2 := by
    have heq : p ⁻¹' {n} = c.bundle.proj ⁻¹' {B.symm n} := by
      ext q
      change B (c.bundle.proj q) = n ↔ c.bundle.proj q = B.symm n
      exact B.toEquiv.eq_symm_apply.symm
    rw [heq]
    exact c.fiber_ncard _
  obtain ⟨hq, hconn, hqcard⟩ :=
    hp.exists_two_sheet_pullback_of_common_deformation hDN H hr K hs htwo
  let : ConnectedSpace (CoveringPullback.Total p f) := hconn
  exact hterminal (CoveringPullback.Total p f) (CoveringPullback.proj p f) hq hqcard

end PreAbstractSimplicialComplex.ModTwoEdgeCocycle

namespace Geometry.SimplicialComplex

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  {G : Type v} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

theorem edgeCocycle_isCoboundary_of_terminal_common_deformation
    (L : SimplicialComplex ℝ G) [Finite L.vertices]
    {N D : Set X} (hDN : D ⊆ N)
    {r : C(X, X)} (H : (ContinuousMap.id X).HomotopyRel r D)
    (hr : ∀ x, r x ∈ D)
    {s : C(N, N)}
    (K : (ContinuousMap.id N).HomotopyRel s (Subtype.val ⁻¹' D))
    (hs : ∀ n, (s n : X) ∈ D) (J : N ≃ₜ L.space)
    (hterminal : ∀ (Y : Type (max u v)) [TopologicalSpace Y]
      [T2Space Y] [ConnectedSpace Y] (p : Y → X),
      IsCoveringMap p → (∀ x, (p ⁻¹' {x}).ncard = 2) → False)
    (c : L.vertexAbstractComplex.toPreAbstractSimplicialComplex.ModTwoEdgeCocycle) :
    c.IsCoboundary := by
  classical
  let : Fintype L.vertices := Fintype.ofFinite _
  exact c.isCoboundary_of_terminal_common_deformation L.vertexAbstractComplex.singleton_mem
    hDN H hr K hs (L.finiteBarycentricHomeomorph.trans J.symm) hterminal

end Geometry.SimplicialComplex
