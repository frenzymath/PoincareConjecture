import PoincareConjecture.Proofs.M04.KoszulPairing
import PoincareConjecture.Proofs.M04.MetricPairings
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivWithinAt_metricGram_along (D : LeviCivitaData g)
    (B : (x : M) → EuclideanSpace ℝ (Fin n) →L[ℝ] TangentSpace (𝓡 n) x)
    {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b) {γ : ℝ → M}
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (𝓡 n) γ (Icc a b) t)
    (hB : ∀ v, ContMDiffAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (fun x => B x v)) (γ t)) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∃ G' : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ,
      HasDerivWithinAt
        (fun s => (g.inner (γ s)).bilinearComp (B (γ s)) (B (γ s)))
        G' (Icc a b) t ∧
      ∀ v w,
        G' v w =
          g.inner (γ t)
            (D.connection (fun x => B x v) (γ t)
              (mfderivWithin 𝓘(ℝ, ℝ) (𝓡 n) γ (Icc a b) t 1))
            (B (γ t) w) +
          g.inner (γ t) (B (γ t) v)
            (D.connection (fun x => B x w) (γ t)
              (mfderivWithin 𝓘(ℝ, ℝ) (𝓡 n) γ (Icc a b) t 1)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let H : M → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    fun x => (g.inner x).bilinearComp (B x) (B x)
  let T : TangentSpace (𝓡 n) (γ t) :=
    mfderivWithin 𝓘(ℝ, ℝ) (𝓡 n) γ (Icc a b) t 1
  have hH : ContMDiffAt (𝓡 n)
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) ∞ H (γ t) := by
    apply contMDiffAt_clm_of_apply
    intro v
    apply contMDiffAt_clm_of_apply
    intro w
    exact (hB v).inner_bundle (hB w)
  let G' : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    derivWithin (fun s => H (γ s)) (Icc a b) t
  have hG : HasDerivWithinAt (fun s => H (γ s)) G' (Icc a b) t := by
    have hd : DifferentiableWithinAt ℝ (fun s => H (γ s)) (Icc a b) t :=
      ((hH.mdifferentiableAt (by simp)).comp_mdifferentiableWithinAt
        t hγ).differentiableWithinAt
    exact hd.hasFDerivWithinAt.hasDerivWithinAt
  refine ⟨G', hG, ?_⟩
  intro v w
  have hY := (hB v).mdifferentiableAt (by simp)
  have hZ := (hB w).mdifferentiableAt (by simp)
  let q : M → ℝ := fun x => g.inner x (B x v) (B x w)
  have hq : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) q (γ t) :=
    hY.inner_bundle hZ
  have hscalar : HasDerivWithinAt (fun s => q (γ s))
      (mvfderiv (𝓡 n) q (γ t) T) (Icc a b) t := by
    have hc := hq.hasMFDerivAt.comp_hasMFDerivWithinAt t hγ.hasMFDerivWithinAt
    have hd : HasFDerivWithinAt (fun s => q (γ s))
        ((mvfderiv (𝓡 n) q (γ t)).comp
          (mfderivWithin 𝓘(ℝ, ℝ) (𝓡 n) γ (Icc a b) t)) (Icc a b) t :=
      hc.hasFDerivWithinAt
    exact hd.hasDerivWithinAt
  have heval : HasDerivWithinAt (fun s => q (γ s)) (G' v w) (Icc a b) t := by
    simpa only [H, q, ContinuousLinearMap.bilinearComp_apply, map_zero, add_zero] using!
      (hG.clm_apply (hasDerivWithinAt_const t (Icc a b) v)).clm_apply
        (hasDerivWithinAt_const t (Icc a b) w)
  have hu := (uniqueDiffOn_Icc hab).uniqueDiffWithinAt ht
  calc
    G' v w = mvfderiv (𝓡 n) q (γ t) T :=
      (heval.derivWithin hu).symm.trans (hscalar.derivWithin hu)
    _ = _ := metric_derivative_pairing D (fun _ => T) hY hZ

end PoincareConjecture.M04
