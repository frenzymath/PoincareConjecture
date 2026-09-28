import PoincareConjecture.Proofs.M15.Mathlib.CompactCubicComparison
import PoincareConjecture.Proofs.M04.CurvatureEnergyHeat
import PoincareConjecture.Proofs.M04.ShiCutoffMaximum

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M15

set_option maxHeartbeats 800000 in

theorem compact_curvature_le_two_of_initial_bound
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [CompactSpace M] (hn : 0 < n) {T : ℝ} (hT : 0 < T)
    (F : RicciFlow n M (Icc 0 T))
    (hinit : ∀ q : M, (F.connection 0).curvatureTensorNorm q ≤ 1) :
    ∀ t ∈ Icc 0 (min T (1 / (32 * (n : ℝ)^6))), ∀ q : M,
      (F.connection t).curvatureTensorNorm q ≤ 2 := by
  let N : M → ℝ → ℝ := fun q t => (F.connection t).curvatureTensorNorm q
  let C : ℝ := 16 * (n : ℝ)^6
  let b : ℝ := min T (1 / (32 * (n : ℝ)^6))
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hC : 0 < C := mul_pos (by norm_num) (pow_pos hnR _)
  have hb : 0 ≤ b := le_min hT.le (by positivity)
  have hsub : Icc 0 b ⊆ Icc 0 T := fun _ ht => ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
  have hbC : b ≤ 1 / (2 * C) := by
    calc
      b ≤ 1 / (32 * (n : ℝ)^6) := min_le_right _ _
      _ = 1 / (2 * C) := by dsimp only [C]; ring
  have hnonneg (q : M) (t : ℝ) : 0 ≤ N q t := Real.sqrt_nonneg _
  have hE : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => N p.2 p.1 ^ 2) (Icc 0 T ×ˢ univ) := by
    simpa only [N, LeviCivitaData.curvatureDerivativeNorm_zero] using
      M04.contMDiffOn_flow_curvatureDerivativeEnergy F 0
  have hN : ContinuousOn (Function.uncurry N) (univ ×ˢ Icc 0 b) := by
    have hswap := hE.continuousOn.comp continuous_swap.continuousOn
      (show MapsTo Prod.swap (univ ×ˢ Icc 0 b) (Icc 0 T ×ˢ univ) from
        fun _ hp => ⟨hsub hp.2, mem_univ _⟩)
    apply hswap.sqrt.congr
    intro p hp
    exact (Real.sqrt_sq (hnonneg p.1 p.2)).symm
  have htime (q : M) : ContDiffOn ℝ ∞ (fun t => N q t ^ 2) (Icc 0 T) := by
    have hslice : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun t : ℝ => (t, q)) := contMDiff_id.prodMk contMDiff_const
    exact (hE.comp hslice.contMDiffOn (fun _ ht => ⟨ht, mem_univ q⟩)).contDiffOn
  have hspace (t : ℝ) :
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun q => N q t ^ 2) := by
    have hnorm : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
        (fun q => ((F.connection t).curvatureDerivativeNorm 0 q)^2) :=
      M04.contMDiff_tensorNorm_sq (F.metric t)
        (M04.isSmoothCovariantTensor_riemannEvaluation (F.connection t))
    simpa only [LeviCivitaData.curvatureDerivativeNorm_zero] using hnorm
  have hbound := Poincare.Parabolic.norm_le_two_of_sq_deriv_le_cube_at_max
    (N := N) (D := fun q t => derivWithin (fun s => N q s ^ 2) (Icc 0 T) t)
    hC hb hbC hN (fun q t _ => hnonneg q t)
    (fun q t ht =>
      (((htime q).differentiableOn (by simp)) t (hsub ⟨ht.1.le, ht.2⟩)).hasDerivWithinAt.mono hsub)
    (fun q t ht hmax => by
      have htT := hsub ⟨ht.1.le, ht.2⟩
      have hmaxsq : IsLocalMax (fun z => N z t ^ 2) q :=
        Filter.Eventually.of_forall (fun z =>
          pow_le_pow_left₀ (hnonneg z t) (hmax z) 2)
      have hlap := M04.laplacian_nonpos_of_isLocalMax (F.connection t)
        (hspace t).contMDiffAt hmaxsq
      have hheat := M04.curvatureEnergy_heat_inequality F htT q
      change derivWithin (fun s => N q s ^ 2) (Icc 0 T) t ≤
        (F.connection t).laplacian (fun z => N z t ^ 2) q -
          2 * ((F.connection t).curvatureDerivativeNorm 1 q)^2 + C * N q t ^ 3 at hheat
      nlinarith [sq_nonneg ((F.connection t).curvatureDerivativeNorm 1 q)]) hinit
  intro t ht q
  exact hbound q t ht

end PoincareConjecture.Proofs.M15
