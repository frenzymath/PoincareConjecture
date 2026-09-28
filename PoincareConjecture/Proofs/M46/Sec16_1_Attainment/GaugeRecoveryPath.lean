import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.GaugeRecoveryDensity
import PoincareConjecture.Proofs.M08.PathGluing









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}




theorem gauge_recovery_path (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    {T tau : ℝ} (htau : 0 < tau) {x y : G.Point}
    {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : Monotone t)
    (hzero : t 0 = 0) (hlast : t (Fin.last m) = Real.sqrt tau)
    (g : ℝ → G.Point)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel 3) ∞ g (Icc 0 (Real.sqrt tau)))
    (hclock : ∀ s ∈ Icc 0 (Real.sqrt tau), G.spacetime.timeFunction (g s) = T - s ^ 2)
    (hx : g 0 = x) (hy : g (Real.sqrt tau) = y)
    (j : Fin m → G.gaugeCover.index)
    (theta : ∀ i, ℝ → (G.timeIntervals.interval (G.gaugeCover.interval (j i))).Point)
    (alpha : ∀ i, ℝ → G.gaugeCover.spatial (j i))
    (htheta : ∀ i, ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡∂ 1) 1 (theta i)
      (Icc (t i.castSucc) (t i.succ)))
    (halpha : ∀ i, ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 3) 1 (alpha i)
      (Icc (t i.castSucc) (t i.succ)))
    (hpieces : ∀ i, EqOn g
      (fun s => (G.gaugeCover.cylinder (j i)).toSpacetime (theta i s, alpha i s))
      (Icc (t i.castSucc) (t i.succ)))
    (v : ∀ i, M08.ChartL2 (EuclideanSpace ℝ (Fin 3)) (t i.castSucc) (t i.succ))
    (hv : ∀ i, (v i : ℝ → EuclideanSpace ℝ (Fin 3))
      =ᵐ[volume.restrict (Icc (t i.castSucc) (t i.succ))]
        deriv (fun r => (alpha i r).val)) :
    ∃ p : M14BackwardPath G T 0 tau x y,
      p.curve = (fun s => g (Real.sqrt s)) ∧
      M14BackwardLAction G p = ∑ i, gaugeCylinderAction (j i) (theta i) (alpha i) (v i) := by
  let C := Icc 0 (Real.sqrt tau)
  have hsub : M14SqrtParameterInterval 0 tau ⊆ C := by
    simp only [M14SqrtParameterInterval, Real.sqrt_zero, C, Subset.rfl]
  have hgclock : ∀ s ∈ M14SqrtParameterInterval 0 tau,
      G.spacetime.timeFunction (g s) = T - s ^ 2 := fun s hs => hclock s (hsub hs)
  have hgx : g (Real.sqrt 0) = x := by simpa only [Real.sqrt_zero] using hx
  let p := M14.backwardPathOfSquareCurveBetween hM12 (le_refl 0) htau g
    (hg.mono hsub) hgclock hgx hy
  have haction : (∫ s in 0..Real.sqrt tau, M14.squareCurveDensity G g C s) =
      M14BackwardLAction G p := by
    simpa only [Real.sqrt_zero] using M14.integral_squareCurveDensity_eq_action_between
      hM12 (le_refl 0) htau g hg hsub hgclock hgx hy
  have hdensity := M14.squareCurveDensity_contDiffOn hM12
    (uniqueDiffOn_Icc (Real.sqrt_pos.mpr htau)) hg
  have hint : IntervalIntegrable (M14.squareCurveDensity G g C) volume 0 (Real.sqrt tau) :=
    hdensity.continuousOn.intervalIntegrable_of_Icc (Real.sqrt_nonneg tau)
  have hab (i : Fin m) : t i.castSucc ≤ t i.succ := ht (Fin.castSucc_le_succ i)
  have hpieceSub (i : Fin m) : Icc (t i.castSucc) (t i.succ) ⊆ C :=
    Icc_subset_Icc (hzero ▸ ht (Fin.zero_le _)) (hlast ▸ ht (Fin.le_last _))
  have hpieceInt (i : Fin m) : IntervalIntegrable (M14.squareCurveDensity G g C) volume
      (t i.castSucc) (t i.succ) := hint.mono_set (by
    rw [uIcc_of_le (hab i), uIcc_of_le (Real.sqrt_nonneg tau)]
    exact hpieceSub i)
  refine ⟨p, rfl, ?_⟩
  rw [← haction]
  calc
    _ = ∫ s in t 0..t (Fin.last m), M14.squareCurveDensity G g C s := by rw [hzero, hlast]
    _ = ∑ i : Fin m, ∫ s in t i.castSucc..t i.succ, M14.squareCurveDensity G g C s :=
      (M08.integrable_sum_fin_partition t _ hpieceInt).2.symm
    _ = _ := Finset.sum_congr rfl (fun i _ =>
      (gauge_recovery_piece_action hM12 (j i) (hab i) (theta i) (alpha i) g (hpieceSub i)
        (htheta i) (halpha i) (hpieces i) (hpieceInt i) (v i) (hv i)).symm)

end PoincareConjecture.Proofs.M46
