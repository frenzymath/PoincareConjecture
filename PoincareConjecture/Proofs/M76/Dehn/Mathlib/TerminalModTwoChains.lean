import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ModTwoCocycleOfClosed
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TerminalCocycleExactness
import Mathlib.Algebra.Field.ZMod












set_option autoImplicit false

universe u v

open Set

namespace PreAbstractSimplicialComplex.ModTwoCochains

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  {ι : Type v} [Fintype ι] (A : PreAbstractSimplicialComplex ι)
  (hvertex : ∀ i : ι, {i} ∈ A.faces)
  {N D : Set X} (hDN : D ⊆ N)
  {r : C(X, X)} (H : (ContinuousMap.id X).HomotopyRel r D)
  (hr : ∀ x, r x ∈ D)
  {s : C(N, N)}
  (K : (ContinuousMap.id N).HomotopyRel s (Subtype.val ⁻¹' D))
  (hs : ∀ n, (s n : X) ∈ D) (B : A.barycentricSpace ≃ₜ N)
  (hterminal : ∀ (Y : Type (max u v)) [TopologicalSpace Y]
    [T2Space Y] [ConnectedSpace Y] (p : Y → X),
    IsCoveringMap p → (∀ x, (p ⁻¹' {x}).ncard = 2) → False)

include hvertex hDN H hr K hs B hterminal




theorem ker_edgeCoboundary_eq_range_vertexCoboundary :
    LinearMap.ker (edgeCoboundary A) = LinearMap.range (vertexCoboundary A) := by
  apply le_antisymm
  · intro z hz
    have hz' : edgeCoboundary A z = 0 := hz
    let c := cocycleOfClosed A z hz'
    have hc : c.IsCoboundary := c.isCoboundary_of_terminal_common_deformation
      hvertex hDN H hr K hs B hterminal
    exact mem_range_vertexCoboundary_of_coboundary A z hz' hc
  · rintro _ ⟨a, rfl⟩
    exact edgeCoboundary_vertexCoboundary A a





theorem range_boundary2_eq_ker_boundary1 :
    LinearMap.range (edgeCoboundary A).dualMap =
      LinearMap.ker (vertexCoboundary A).dualMap := by
  have hcochain := ker_edgeCoboundary_eq_range_vertexCoboundary A
    hvertex hDN H hr K hs B hterminal
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker (edgeCoboundary A), hcochain,
    LinearMap.ker_dualMap_eq_dualAnnihilator_range (vertexCoboundary A)]



theorem exists_triangle_chain_of_cycle
    (z : Module.Dual (ZMod 2) (Edge A → ZMod 2))
    (hz : (vertexCoboundary A).dualMap z = 0) :
    ∃ t : Module.Dual (ZMod 2) (Triangle A → ZMod 2),
      (edgeCoboundary A).dualMap t = z := by
  have hmem : z ∈ LinearMap.ker (vertexCoboundary A).dualMap := hz
  rw [← range_boundary2_eq_ker_boundary1 A hvertex hDN H hr K hs B hterminal] at hmem
  exact hmem

end PreAbstractSimplicialComplex.ModTwoCochains
