import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.ClosedMarkedLift
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TerminalCocycleExactness
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false

universe u v

open Set Metric PoincareConjecture.M76.Dehn

namespace PreAbstractSimplicialComplex.ModTwoCochains

local notation "Q2" => sphere (0 : Fin 2 → ℝ) 1

theorem finrank_closed_le_coboundaries_add_one_of_marked_loop
    {X : Type u} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    {ι : Type v} [Fintype ι] (A : PreAbstractSimplicialComplex ι)
    (hvertex : ∀ i : ι, {i} ∈ A.faces)
    {N D : Set X} (hDN : D ⊆ N)
    {r : C(X, X)} (H : (ContinuousMap.id X).HomotopyRel r D)
    (hr : ∀ x, r x ∈ D)
    {s : C(N, N)}
    (K : (ContinuousMap.id N).HomotopyRel s (Subtype.val ⁻¹' D))
    (hs : ∀ n, (s n : X) ∈ D)
    (B : A.barycentricSpace ≃ₜ N)
    (γ : C(Q2, X)) (hγ : ∀ z, γ z ∈ D)
    (hterminal : ∀ (Y : Type (max u v)) [TopologicalSpace Y]
      [T2Space Y] [ConnectedSpace Y] (p : Y → X),
      IsCoveringMap p → (∀ x, (p ⁻¹' {x}).ncard = 2) →
      ∀ lift : C(Q2, Y), (∀ z, p (lift z) = γ z) → False) :
    Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary A)) ≤
      Module.finrank (ZMod 2) (LinearMap.range (vertexCoboundary A)) + 1 := by
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
  let δ : C(Q2, A.barycentricSpace) :=
    ⟨fun z => B.symm ⟨γ z, hDN (hγ z)⟩,
      B.symm.continuous.comp (γ.continuous.subtype_mk _)⟩
  let E := closedCochainEvaluation A
    (Path.Homotopic.Quotient.mk (squareRimLoop.map δ.continuous))
  have hker (z : LinearMap.ker (edgeCoboundary A)) (hz : E z = 0) :
      (z : Edge A → ZMod 2) ∈ LinearMap.range (vertexCoboundary A) := by
    apply mem_range_vertexCoboundary_of_coboundary A z z.property
    let c := cocycleOfClosed A z z.property
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
    obtain ⟨q, hqγ⟩ := c.exists_squareRim_lift_of_pathValue_eq_zero δ hz
    have hcompat (z : Q2) : f (γ z) = p (q z) := by
      change f (γ z) = B (c.bundle.proj (q z))
      rw [hqγ]
      change f (γ z) = B (B.symm ⟨γ z, hDN (hγ z)⟩)
      rw [B.apply_symm_apply]
      exact Subtype.ext (hfix (γ z) (hγ z))
    let lift : C(Q2, CoveringPullback.Total p f) :=
      ⟨fun z => ⟨(γ z, q z), hcompat z⟩,
        (γ.continuous.prodMk q.continuous).subtype_mk _⟩
    exact hterminal (CoveringPullback.Total p f) (CoveringPullback.proj p f)
      hq hqcard lift (fun _ => rfl)
  let T : LinearMap.ker E →ₗ[ZMod 2] LinearMap.range (vertexCoboundary A) :=
    { toFun := fun z => ⟨z.val.val, hker z.val z.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hT : Function.Injective T := by
    intro z w h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun t : LinearMap.range (vertexCoboundary A) => t.val) h
  have hk := LinearMap.finrank_le_finrank_of_injective hT
  have hdim : Module.finrank (ZMod 2) (LinearMap.range E) ≤ 1 := by
    simpa using (LinearMap.range E).finrank_le
  have heq := LinearMap.finrank_range_add_finrank_ker (K := ZMod 2) E
  omega

end PreAbstractSimplicialComplex.ModTwoCochains
