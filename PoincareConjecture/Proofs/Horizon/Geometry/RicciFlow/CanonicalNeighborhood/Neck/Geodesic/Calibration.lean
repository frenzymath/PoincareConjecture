import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck


set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem RiemannianMetric.edist_le_intrinsicEDist (g : RiemannianMetric 3 M)
    (U : Set M) (x y : M) : g.edist x y ≤ intrinsicEDist g U x y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply le_sInf
  rintro l ⟨γ, hγ, h0, h1, _, rfl⟩
  exact Manifold.riemannianEDist_le_pathELength hγ h0 h1 zero_le_one

theorem intrinsic_minimality_of_calibration {U : Set M} {f : M → ℝ}
    {γ : ℝ → M} {L : ℝ}
    (hcal : ∀ t ∈ Icc 0 L, f (γ t) = f (γ 0) - t)
    (hLip : ∀ x y, |f x - f y| ≤ (g.edist x y).toReal) :
    ∀ a ∈ Icc (0 : ℝ) L, ∀ b ∈ Icc (0 : ℝ) L, a ≤ b →
      ENNReal.ofReal (b - a) ≤ intrinsicEDist g U (γ a) (γ b) := by
  intro a ha b hb hab
  have h := hLip (γ a) (γ b)
  rw [hcal a ha, hcal b hb, sub_sub_sub_cancel_left,
    abs_of_nonneg (sub_nonneg.mpr hab)] at h
  exact (ENNReal.ofReal_le_ofReal h).trans
    (ENNReal.ofReal_toReal_le.trans (g.edist_le_intrinsicEDist U (γ a) (γ b)))

end PoincareConjecture
