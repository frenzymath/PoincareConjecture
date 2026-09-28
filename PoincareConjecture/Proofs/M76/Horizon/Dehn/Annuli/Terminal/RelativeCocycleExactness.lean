import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Terminal.CocycleSections
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TerminalCocycleExactness

set_option autoImplicit false

universe u v w

open Set

namespace PreAbstractSimplicialComplex.ModTwoEdgeCocycle

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  {ι : Type v} [Fintype ι] {A : PreAbstractSimplicialComplex ι}
  {Z : Type w} [TopologicalSpace Z]

theorem isCoboundary_of_marked_terminal_common_deformation
    (c : A.ModTwoEdgeCocycle) (hvertex : ∀ i : ι, {i} ∈ A.faces)
    {N D : Set X} (hDN : D ⊆ N)
    {r : C(X, X)} (H : (ContinuousMap.id X).HomotopyRel r D)
    (hr : ∀ x, r x ∈ D)
    {s : C(N, N)}
    (K : (ContinuousMap.id N).HomotopyRel s (Subtype.val ⁻¹' D))
    (hs : ∀ n, (s n : X) ∈ D)
    (B : A.barycentricSpace ≃ₜ N)
    (γ : C(Z, X)) (hγ : ∀ z, γ z ∈ D)
    (a : ι → ZMod 2)
    (ha : ∀ z i j,
      B.symm ⟨γ z, hDN (hγ z)⟩ ∈ A.openVertexStar i →
      B.symm ⟨γ z, hDN (hγ z)⟩ ∈ A.openVertexStar j →
      c.value i j = a i + a j)
    (hterminal : ∀ (Y : Type (max u v)) [TopologicalSpace Y]
      [T2Space Y] [ConnectedSpace Y] (p : Y → X),
      IsCoveringMap p → (∀ x, (p ⁻¹' {x}).ncard = 2) →
      ∀ lift : C(Z, Y), (∀ z, p (lift z) = γ z) → False) :
    c.IsCoboundary := by
  classical
  let f : C(X, N) := ⟨fun x => ⟨r x, hDN (hr x)⟩, r.continuous.subtype_mk _⟩
  have hfix (x : X) (hx : x ∈ D) : r x = x := by
    rw [← H.toHomotopy.apply_one x]
    exact H.eq_fst 1 hx
  have hfrange : range f = Subtype.val ⁻¹' D := by
    ext n
    constructor
    · rintro ⟨x, rfl⟩
      exact hr x
    · intro hn
      exact ⟨n, Subtype.ext (hfix n hn)⟩
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
  let δ : C(Z, A.barycentricSpace) :=
    ⟨fun z => B.symm ⟨γ z, hDN (hγ z)⟩,
      B.symm.continuous.comp (γ.continuous.subtype_mk _)⟩
  obtain ⟨q, hqγ⟩ := c.exists_lift_of_star_potential δ a ha
  have hcompat (z : Z) : f (γ z) = p (q z) := by
    change f (γ z) = B (c.bundle.proj (q z))
    rw [hqγ]
    change f (γ z) = B (B.symm ⟨γ z, hDN (hγ z)⟩)
    rw [B.apply_symm_apply]
    exact Subtype.ext (hfix (γ z) (hγ z))
  let lift : C(Z, CoveringPullback.Total p f) :=
    ⟨fun z => ⟨(γ z, q z), hcompat z⟩,
      (γ.continuous.prodMk q.continuous).subtype_mk _⟩
  exact hterminal (CoveringPullback.Total p f) (CoveringPullback.proj p f)
    hq hqcard lift (fun _ => rfl)

end PreAbstractSimplicialComplex.ModTwoEdgeCocycle
