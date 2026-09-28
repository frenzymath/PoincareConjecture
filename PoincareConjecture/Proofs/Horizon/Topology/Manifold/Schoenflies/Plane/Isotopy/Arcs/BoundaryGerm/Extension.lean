import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.BoundaryGerm.Differential
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Germ.Stationary



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.BoundaryGerm

private abbrev E2 := EuclideanSpace Real (Fin 2)



theorem exists_supported_extension_of_inward_circle_patch
    {D : E2 -> E2} (hD : ContDiff Real ∞ D)
    {P K U V : Set E2} (hP : IsCompact P) (hK : IsCompact K) (hKP : K ⊆ P)
    (hV : IsOpen V) (hPV : P ⊆ V ∩ sphere (0 : E2) 1)
    (hfix : ∀ x ∈ V ∩ sphere (0 : E2) 1, D x = x)
    (hinj : ∀ x ∈ P, Injective (fderiv Real D x))
    (hinside : ∀ x ∈ P, ∀ᶠ s in 𝓝[<] (0 : Real), ‖D ((1 + s) • x)‖ ≤ 1)
    (hU : IsOpen U) (hKU : K ⊆ U) (hUP : U ∩ sphere (0 : E2) 1 ⊆ P) :
    ∃ S : Set E2, IsCompact S ∧ S ⊆ U ∧
      ∃ W : Set E2, IsOpen W ∧ K ⊆ W ∧
        ∃ F : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
          (∀ x ∉ S, F x = x) ∧ EqOn F D W ∧
          ∀ x ∈ sphere (0 : E2) 1, F x = x := by
  apply Reverse.exists_supported_germ_of_stationary hD hP hK hKP
    (fun x hx => hfix x (hPV hx)) _ hU hKU hUP
  intro t ht x hx
  exact bijective_fderiv_homotopy_of_inward_circle_patch hD hV hfix
    ⟨x, (hPV hx).2⟩ (hPV hx).1 (hinj x hx) (hinside x hx) ht

end Poincare.Manifold.Schoenflies.PlaneArcs.BoundaryGerm
