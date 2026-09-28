import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.BallMatching.Chart
import Mathlib.Analysis.InnerProductSpace.Calculus
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.Restriction

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

theorem exists_supported_matching_inside_ball {n : Nat}
    (A B C : Diffeomorph (𝓡 n) (𝓡 n)
      (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n)) ∞)
    (hA : A '' closedBall 0 1 ⊆ C '' ball 0 1)
    (hB : B '' closedBall 0 1 ⊆ C '' ball 0 1) :
    ∃ K : Set (EuclideanSpace Real (Fin n)), IsCompact K ∧ K ⊆ C '' ball 0 1 ∧
      ∃ D : Diffeomorph (𝓡 n) (𝓡 n)
        (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n)) ∞,
        (∀ x ∉ K, D x = x) ∧
        D '' (A '' closedBall 0 1) = B '' closedBall 0 1 := by
  let E := EuclideanSpace Real (Fin n)
  let u : OpenPartialHomeomorph E E := OpenPartialHomeomorph.univUnitBall
  let e := u.trans C.toHomeomorph.toOpenPartialHomeomorph
  have hes : e.source = univ := by
    ext x
    change (x ∈ (univ : Set E) ∧ u x ∈ (univ : Set E)) ↔ x ∈ univ
    simp
  have het : e.target = C '' ball 0 1 := by
    ext x
    change (x ∈ (univ : Set E) ∧ C.symm x ∈ ball (0 : E) 1) ↔ x ∈ C '' ball 0 1
    constructor
    · intro hx
      exact ⟨C.symm x, hx.2, C.apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨mem_univ _, by simpa only [C.symm_apply_apply] using hy⟩
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source :=
    (C.contMDiff.comp OpenPartialHomeomorph.contDiff_univUnitBall.contMDiff).contMDiffOn
  have hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target :=
    OpenPartialHomeomorph.contDiffOn_univUnitBall_symm.contMDiffOn.comp
      C.symm.contMDiff.contMDiffOn (fun _ hx => hx.2)
  obtain ⟨_, K, hK, hKe, D, hfix, _, hD⟩ :=
    exists_supported_matching_of_balls_in_chart e hes he hei A B (by norm_num)
      (het.symm ▸ hA) (het.symm ▸ hB)
  exact ⟨K, hK, het ▸ hKe, D, hfix, hD⟩

theorem exists_matching_of_nested_balls {n : Nat}
    (A₀ A₁ B₀ B₁ : Diffeomorph (𝓡 n) (𝓡 n)
      (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n)) ∞)
    (hA : A₁ '' closedBall 0 1 ⊆ A₀ '' ball 0 1)
    (hB : B₁ '' closedBall 0 1 ⊆ B₀ '' ball 0 1) :
    ∃ D : Diffeomorph (𝓡 n) (𝓡 n)
        (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n)) ∞,
      D '' (A₀ '' closedBall 0 1) = B₀ '' closedBall 0 1 ∧
      D '' (A₁ '' closedBall 0 1) = B₁ '' closedBall 0 1 ∧
      ∀ x ∉ ball (0 : EuclideanSpace Real (Fin n)) 1, D (A₀ x) = B₀ x := by
  let P := A₀.symm.trans B₀
  let A := A₁.trans P
  have hP (x : EuclideanSpace Real (Fin n)) : P (A₀ x) = B₀ x := by
    change B₀ (A₀.symm (A₀ x)) = B₀ x
    rw [A₀.symm_apply_apply]
  have hPA : A '' closedBall 0 1 ⊆ B₀ '' ball 0 1 := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hA ⟨x, hx, rfl⟩
    refine ⟨y, hy, ?_⟩
    change B₀ y = P (A₁ x)
    rw [← hxy, hP]
  obtain ⟨K, _, hK, F, hfix, hF⟩ := exists_supported_matching_inside_ball A B₁ B₀ hPA hB
  let D := P.trans F
  have hFfix (x : EuclideanSpace Real (Fin n)) (hx : x ∉ B₀ '' ball 0 1) : F x = x :=
    hfix x (fun h => hx (hK h))
  have hFclosed : F '' (B₀ '' closedBall 0 1) = B₀ '' closedBall 0 1 := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      by_contra hout
      have hnot : F x ∉ B₀ '' ball 0 1 := fun h =>
        hout (image_mono ball_subset_closedBall h)
      have heq : F x = x := F.injective (hFfix (F x) hnot)
      exact hout (heq.symm ▸ hx)
    · intro x hx
      refine ⟨F.symm x, ?_, F.apply_symm_apply x⟩
      by_contra hout
      have heq := hFfix (F.symm x) (fun h => hout (image_mono ball_subset_closedBall h))
      rw [F.apply_symm_apply] at heq
      exact hout (heq ▸ hx)
  refine ⟨D, ?_, ?_, ?_⟩
  · calc
      D '' (A₀ '' closedBall 0 1) = F '' ((P ∘ A₀) '' closedBall 0 1) := by
        rw [image_image, image_image]
        rfl
      _ = F '' (B₀ '' closedBall 0 1) := by rw [show P ∘ A₀ = B₀ from funext hP]
      _ = B₀ '' closedBall 0 1 := hFclosed
  · calc
      D '' (A₁ '' closedBall 0 1) = F '' (A '' closedBall 0 1) := by
        rw [image_image, image_image]
        rfl
      _ = B₁ '' closedBall 0 1 := hF
  · intro x hx
    change F (P (A₀ x)) = B₀ x
    rw [hP]
    apply hFfix
    rintro ⟨y, hy, hyx⟩
    exact hx (B₀.injective hyx ▸ hy)

end Poincare.Manifold.Schoenflies
