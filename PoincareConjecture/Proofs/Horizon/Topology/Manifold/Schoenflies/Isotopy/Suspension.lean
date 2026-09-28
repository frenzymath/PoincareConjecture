import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.BallExtension.ParametricInverse
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies




theorem exists_supported_family_suspension
    {n : Nat}
    (Phi : Real -> Diffeomorph (𝓡 n) (𝓡 n)
      (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n)) ∞)
    (hPhi : ContDiff Real ∞
      (fun z : Real × EuclideanSpace Real (Fin n) => Phi z.1 z.2))
    (hzero : ∀ x, Phi 0 x = x)
    {K : Set (EuclideanSpace Real (Fin n))}
    (hK : IsCompact K)
    (hfix : ∀ t x, x ∉ K -> Phi t x = x)
    {r R : Real} (hr : 0 < r) (hrR : r < R) :
    ∃ F : Diffeomorph
        𝓘(Real, Real × EuclideanSpace Real (Fin n))
        𝓘(Real, Real × EuclideanSpace Real (Fin n))
        (Real × EuclideanSpace Real (Fin n)) (Real × EuclideanSpace Real (Fin n)) ∞,
      (∀ z, (F z).1 = z.1) ∧
      (∀ t ∈ closedBall (0 : Real) r, ∀ x, F (t, x) = (t, Phi t x)) ∧
      IsCompact (closedBall (0 : Real) R ×ˢ K) ∧
      ∀ z ∉ closedBall (0 : Real) R ×ˢ K, F z = z := by
  let χ : ContDiffBump (0 : Real) := ⟨r, R, hr, hrR⟩
  let a : Real -> Real := fun t => χ t * t
  have ha : ContDiff Real ∞ a := χ.contDiff.mul contDiff_id
  have hPm : ContMDiff (𝓘(Real, Real).prod (𝓡 n)) (𝓡 n) ∞
      (fun z : Real × EuclideanSpace Real (Fin n) => Phi z.1 z.2) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact hPhi.contMDiff
  have hPi := Poincare.Manifold.contMDiff_diffeomorph_family_symm Phi hPm
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hPi
  let F : Diffeomorph
      𝓘(Real, Real × EuclideanSpace Real (Fin n))
      𝓘(Real, Real × EuclideanSpace Real (Fin n))
      (Real × EuclideanSpace Real (Fin n)) (Real × EuclideanSpace Real (Fin n)) ∞ := {
    toEquiv := {
      toFun := fun z => (z.1, Phi (a z.1) z.2)
      invFun := fun z => (z.1, (Phi (a z.1)).symm z.2)
      left_inv := fun z => by simp
      right_inv := fun z => by simp }
    contMDiff_toFun := (contDiff_fst.prodMk
      (hPhi.comp ((ha.comp contDiff_fst).prodMk contDiff_snd))).contMDiff
    contMDiff_invFun := (contDiff_fst.prodMk
      (hPi.contDiff.comp ((ha.comp contDiff_fst).prodMk contDiff_snd))).contMDiff }
  refine ⟨F, fun _ => rfl, ?_, (isCompact_closedBall 0 R).prod hK, ?_⟩
  · intro t ht x
    change (t, Phi (χ t * t) x) = _
    rw [χ.one_of_mem_closedBall ht, one_mul]
  · rintro ⟨t, x⟩ hz
    change (t, Phi (χ t * t) x) = (t, x)
    by_cases ht : t ∈ closedBall (0 : Real) R
    · rw [hfix _ x (fun hx => hz ⟨ht, hx⟩)]
    · rw [χ.zero_of_le_dist (le_of_lt (not_le.mp ht)), zero_mul, hzero]

end Poincare.Manifold.Schoenflies
