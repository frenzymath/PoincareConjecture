import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.NeckLevels.SignedSegments
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Convexity.Gradient.LowerBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem mvfderiv_initial_mul_length_le_of_hessian_ge
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {γ : ℝ → M} {L H : ℝ} (hL : 0 ≤ L)
    (hγ : g.IsGeodesicOn γ (Icc 0 L))
    (hspeed : ∀ t ∈ Icc 0 L,
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = 1)
    (hhess : ∀ t ∈ Icc 0 L, ∀ v : TangentSpace (𝓡 n) (γ t),
      -H * g.inner (γ t) v v ≤ D.hessian f (γ t) v v) :
    mvfderiv (𝓡 n) f (γ 0) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) * L ≤
      f (γ L) - f (γ 0) + H * L ^ 2 / 2 := by
  let F := (fun x => -f x) ∘ γ
  let V := fun t => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1
  let A := fun t => D.hessian (fun x => -f x) (γ t) (V t) (V t)
  have hfirst (t : ℝ) (ht : t ∈ Icc 0 L) : HasDerivAt F (deriv F t) t := by
    exact ((contMDiffAt_iff_contDiffAt.mp
      ((hf.neg.contMDiffAt.of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)).comp t
        (hγ.contMDiffAt ht))).differentiableAt (by simp)).hasDerivAt
  have hsecond (t : ℝ) (ht : t ∈ Icc 0 L) : HasDerivAt (deriv F) (A t) t :=
    D.hasDerivAt_deriv_comp_geodesic_of_contMDiffOn isOpen_univ hf.neg.contMDiffOn
      hγ ht (mem_univ _)
  have hA (t : ℝ) (ht : t ∈ Icc 0 L) : A t ≤ H := by
    have hnn : 0 ≤ g.inner (γ t) (V t) (V t) := by
      by_cases hv : V t = 0
      · simp [hv]
      · exact (g.pos (γ t) (V t) hv).le
    have hsq := congrArg (fun a : ℝ => a ^ 2) (hspeed t ht)
    change (Real.sqrt (g.inner (γ t) (V t) (V t))) ^ 2 = 1 ^ 2 at hsq
    rw [Real.sq_sqrt hnn, one_pow] at hsq
    have hneg : A t = -D.hessian f (γ t) (V t) (V t) := by
      simpa only [A, neg_one_mul] using D.hessian_const_mul (-1) f (γ t) (V t) (V t)
    rw [hneg]
    have h := hhess t ht (V t)
    rw [hsq, mul_one] at h
    linarith
  have hbound := Poincare.Analysis.quadratic_upper_bound_of_hasDerivAt2_le hL
    hfirst (fun t ht => hsecond t ⟨ht.1.le, ht.2.le⟩)
    (fun t ht => hA t ⟨ht.1.le, ht.2.le⟩)
  have hdu : deriv F 0 =
      -mvfderiv (𝓡 n) f (γ 0) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) := by
    have heq := congrArg (fun A => A (1 : ℝ))
      (mfderiv_comp 0 (hf.neg.contMDiffAt.mdifferentiableAt (by simp))
        ((hγ.contMDiffAt ⟨le_rfl, hL⟩).mdifferentiableAt (by simp)))
    rw [mfderiv_eq_fderiv] at heq
    change deriv F 0 = mvfderiv (𝓡 n) (fun x => -f x) (γ 0)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) at heq
    have hnegderiv : mvfderiv (𝓡 n) (fun x => -f x) (γ 0) =
        -mvfderiv (𝓡 n) f (γ 0) := mvfderiv_neg
    rw [hnegderiv, neg_apply] at heq
    exact heq
  rw [hdu] at hbound
  change -f (γ L) ≤ -f (γ 0) + L *
    (-mvfderiv (𝓡 n) f (γ 0) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1)) + H * L ^ 2 / 2 at hbound
  linarith

theorem abs_mvfderiv_axial_ge_of_signed_alignment
    (D : LeviCivitaData g) (f : M → ℝ) (x : M)
    (v a : TangentSpace (𝓡 n) x) {σ α G l : ℝ}
    (hσ : |σ| = 1) (hα : 0 ≤ α) (hG : 0 ≤ G)
    (halign : g.tangentNorm x (σ • v - a) ≤ α)
    (hgrad : g.tangentNorm x (D.gradient f x) ≤ G)
    (hdecrease : mvfderiv (𝓡 n) f x v ≤ -l) :
    l - G * α ≤ |mvfderiv (𝓡 n) f x a| := by
  have hb := (D.abs_mvfderiv_le_gradient_norm f x (σ • v - a)).trans
    (mul_le_mul hgrad halign (Real.sqrt_nonneg _) hG)
  simp only [map_sub, map_smul, smul_eq_mul] at hb
  have hbig : l ≤ |σ * mvfderiv (𝓡 n) f x v| := by
    rw [abs_mul, hσ, one_mul]
    linarith [neg_le_abs (mvfderiv (𝓡 n) f x v)]
  have htriangle := abs_sub_abs_le_abs_sub
    (σ * mvfderiv (𝓡 n) f x v) (mvfderiv (𝓡 n) f x a)
  linarith

end PoincareConjecture.LeviCivitaData
