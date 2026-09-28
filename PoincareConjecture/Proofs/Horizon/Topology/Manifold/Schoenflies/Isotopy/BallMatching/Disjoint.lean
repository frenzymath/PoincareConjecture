import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.BallMatching.OpenRegion
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.BallExterior



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies



theorem exists_supported_matching_outside_ball {n : Nat}
    (hdim : 1 < Module.rank Real (EuclideanSpace Real (Fin n)))
    (A B C : Diffeomorph (𝓡 n) (𝓡 n)
      (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n)) ∞)
    (hA : Disjoint (A '' closedBall 0 1) (C '' closedBall 0 1))
    (hB : Disjoint (B '' closedBall 0 1) (C '' closedBall 0 1)) :
    ∃ K : Set (EuclideanSpace Real (Fin n)), IsCompact K ∧
      K ⊆ (C '' closedBall 0 1)ᶜ ∧
      ∃ D : Diffeomorph (𝓡 n) (𝓡 n)
        (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n)) ∞,
        (∀ x ∉ K, D x = x) ∧
        D '' (A '' closedBall 0 1) = B '' closedBall 0 1 ∧
        ∀ x ∈ C '' closedBall 0 1, D x = x := by
  have hO : IsOpen (C '' closedBall 0 1)ᶜ :=
    ((isCompact_closedBall _ _).image C.continuous).isClosed.isOpen_compl
  have hc : IsConnected (C '' closedBall 0 1)ᶜ :=
    C.toHomeomorph.toOpenPartialHomeomorph.isConnected_compl_image_closedBall hdim
      (subset_univ _)
  obtain ⟨K, hK, hKO, D, hfix, hD⟩ :=
    exists_supported_matching_of_balls_in_open_region A B _ hO hc
      (fun x hx hCx => disjoint_left.mp hA hx hCx)
      (fun x hx hCx => disjoint_left.mp hB hx hCx)
  exact ⟨K, hK, hKO, D, hfix, hD, fun x hx => hfix x (fun h => hKO h hx)⟩



theorem exists_matching_of_disjoint_balls {n : Nat}
    (hdim : 1 < Module.rank Real (EuclideanSpace Real (Fin n)))
    (A₀ A₁ B₀ B₁ : Diffeomorph (𝓡 n) (𝓡 n)
      (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n)) ∞)
    (hA : Disjoint (A₀ '' closedBall 0 1) (A₁ '' closedBall 0 1))
    (hB : Disjoint (B₀ '' closedBall 0 1) (B₁ '' closedBall 0 1)) :
    ∃ D : Diffeomorph (𝓡 n) (𝓡 n)
        (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n)) ∞,
      D '' (A₀ '' closedBall 0 1) = B₀ '' closedBall 0 1 ∧
      D '' (A₁ '' closedBall 0 1) = B₁ '' closedBall 0 1 ∧
      ∀ x ∈ closedBall (0 : EuclideanSpace Real (Fin n)) 1, D (A₀ x) = B₀ x := by
  let P := A₀.symm.trans B₀
  let A := A₁.trans P
  have hP (x : EuclideanSpace Real (Fin n)) : P (A₀ x) = B₀ x := by
    change B₀ (A₀.symm (A₀ x)) = B₀ x
    rw [A₀.symm_apply_apply]
  have hPA : Disjoint (A '' closedBall 0 1) (B₀ '' closedBall 0 1) := by
    apply disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
    have hxy : A₀ y = A₁ x := P.injective ((hP y).trans heq)
    exact disjoint_left.mp hA ⟨y, hy, hxy⟩ ⟨x, hx, rfl⟩
  obtain ⟨_, _, _, F, _, hF, hFfix⟩ :=
    exists_supported_matching_outside_ball hdim A B₁ B₀ hPA hB.symm
  let D := P.trans F
  have hD (x : EuclideanSpace Real (Fin n)) (hx : x ∈ closedBall 0 1) :
      D (A₀ x) = B₀ x := by
    change F (P (A₀ x)) = B₀ x
    rw [hP, hFfix _ ⟨x, hx, rfl⟩]
  refine ⟨D, ?_, ?_, hD⟩
  · rw [image_image]
    exact (show EqOn (D ∘ A₀) B₀ (closedBall 0 1) from hD).image_eq
  · calc
      D '' (A₁ '' closedBall 0 1) = F '' (A '' closedBall 0 1) := by
        rw [image_image, image_image]
        rfl
      _ = B₁ '' closedBall 0 1 := hF

end Poincare.Manifold.Schoenflies
