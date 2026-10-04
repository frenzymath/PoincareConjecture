import PoincareLib.Topology.Manifold.Surgery.Event.Rotations.Rotations

/-!
# Rotation invariance of standard cap balls

The metric's actual pullback identity preserves lengths of smooth paths.
Taking their infimum gives distance contraction, which suffices to show
that every allowed rotation preserves each ball about the origin.
-/

set_option autoImplicit false

open Set MeasureTheory Manifold
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT.M38

/-- The stored matrix action is globally smooth on the literal cap space. -/
theorem standardRotation_smooth (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (standardRotation A) := by
  rw [standardRotation_eq_toEuclideanLin]
  exact contMDiff_iff_contDiff.mpr A.1.toEuclideanLin.toContinuousLinearMap.contDiff

/-- Standard rotations fix the distinguished cap origin. -/
theorem standardRotation_zero (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    standardRotation A 0 = 0 := by
  rw [standardRotation_eq_toEuclideanLin]
  exact map_zero _

/-- The metric pullback identity preserves the length of each C1 path.
The chain rule is used in the open parameter interval, whose omitted
endpoints have measure zero. -/
theorem standardRotation_pathELength (g₀ : StandardInitialMetric)
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (γ : ℝ → StandardCapSpace) (a b : ℝ)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b)) :
    g₀.metric.pathELength (standardRotation A ∘ γ) a b =
      g₀.metric.pathELength γ a b := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
    ⟨g₀.metric.toRiemannianMetric⟩
  change Manifold.pathELength (𝓡 3) (standardRotation A ∘ γ) a b =
    Manifold.pathELength (𝓡 3) γ a b
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
    Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have hγt : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 3) 1 γ t :=
    hγ.contMDiffAt (Icc_mem_nhds ht.1 ht.2)
  dsimp only
  rw [← ofReal_norm, ← ofReal_norm, norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
  have hchain : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (standardRotation A ∘ γ) t 1 =
      mfderiv (𝓡 3) (𝓡 3) (standardRotation A) (γ t)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1) := by
    exact congrArg (fun f => f 1)
      (mfderiv_comp t ((standardRotation_smooth A).mdifferentiableAt (by simp))
        (hγt.mdifferentiableAt (by simp)))
  rw [hchain]
  change ENNReal.ofReal (Real.sqrt (g₀.metric.inner (standardRotation A (γ t))
    (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) (γ t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1))
    (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) (γ t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1)))) =
    ENNReal.ofReal (Real.sqrt (g₀.metric.inner (γ t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1)))
  rw [g₀.rotation_invariant]

/-- Rotating near-minimizing paths gives the distance inequality needed
for invariance of each actual intrinsic standard cap ball. -/
theorem standardRotation_edist_le (g₀ : StandardInitialMetric)
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (x y : StandardCapSpace) :
    g₀.metric.edist (standardRotation A x) (standardRotation A y) ≤
      g₀.metric.edist x y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
    ⟨g₀.metric.toRiemannianMetric⟩
  apply le_of_forall_gt
  intro r hr
  obtain ⟨γ, hγ0, hγ1, hγ, hlength⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt hr
  have hrot : ContMDiff (𝓡 3) (𝓡 3) 1 (standardRotation A) :=
    (standardRotation_smooth A).of_le (by simp)
  have hsmooth := hrot.comp_contMDiffOn hγ
  have hdist := Manifold.riemannianEDist_le_pathELength hsmooth
    (congrArg (standardRotation A) hγ0) (congrArg (standardRotation A) hγ1) zero_le_one
  have hlength_eq := standardRotation_pathELength g₀ A γ 0 1 hγ
  exact hdist.trans_lt (hlength_eq.trans_lt hlength)

/-- Same-norm points belong together to each actual standard cap ball. -/
theorem standard_ball_radial (g₀ : StandardInitialMetric) (r : ℝ)
    (x : StandardCapSpace) (hx : x ∈ g₀.metric.ball 0 r)
    (y : StandardCapSpace) (h : ‖y‖ = ‖x‖) : y ∈ g₀.metric.ball 0 r := by
  obtain ⟨A, hA⟩ := exists_standardRotation x y h.symm
  have hdist := standardRotation_edist_le g₀ A 0 x
  rw [standardRotation_zero, hA] at hdist
  exact hdist.trans_lt hx

end PoincareMT.M38
