import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.Mathlib.ResolutionEndHomotopies
import PoincareConjecture.Proofs.Horizon.Topology.Covering.Universal.PathHomotopy

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76.Dehn

theorem convex_end_selects_nonnull_spanning_rim
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] {K : Set E} (hK : Convex ℝ K)
    (τ : C(K, X)) {a b a' b' : K}
    (D₀ : Path a a') (D₁ : Path b b') (Q₀ : Path a b) (Q₁ : Path a' b')
    (A : Path (τ a) (τ b)) (B : Path (τ a') (τ b'))
    (hold : ¬ (A.trans ((D₀.map τ.continuous).trans
      (B.trans (D₁.map τ.continuous).symm)).symm).Homotopic (Path.refl (τ a))) :
    ¬ (A.trans (Q₀.map τ.continuous).symm).Homotopic (Path.refl (τ a)) ∨
      ¬ (B.trans (Q₁.map τ.continuous).symm).Homotopic (Path.refl (τ a')) := by
  by_contra h
  push Not at h
  have hA := Path.Homotopic.of_trans_symm h.1
  have hB := Path.Homotopic.of_trans_symm h.2
  have hreplace := hA.hcomp ((Path.Homotopic.refl (D₀.map τ.continuous)).hcomp
    (hB.hcomp (Path.Homotopic.refl (D₁.map τ.continuous).symm))).symm₂
  let P := Q₀.trans (D₀.trans (Q₁.trans D₁.symm)).symm
  have hP : P.Homotopic (Path.refl a) :=
    Path.homotopic_of_convex_range hK Subset.rfl P (Path.refl a)
      (fun t ↦ (P t).property) (fun _ ↦ a.property)
  have hmap := hP.map τ
  simp only [P, Path.map_trans, ← Path.map_symm] at hmap
  exact hold (hreplace.trans hmap)

end PoincareConjecture.M76.Dehn
