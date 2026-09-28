import PoincareConjecture.Proofs.M35.Thm12_28.ScalarMetricJets
import PoincareConjecture.Proofs.M35.Mathlib.FiniteJetOperations
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional

set_option autoImplicit false
set_option maxSynthPendingDepth 5

open Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

local notation:max "E" n:max => EuclideanSpace ℝ (Fin n)

theorem metric_jet_tendsto_of_scalar_jets {n r : ℕ}
    {gseq : ℕ → RiemannianMetric n (E n)} {g : RiemannianMetric n (E n)}
    (pseq : ℕ → E n) (p : E n)
    (hjet : ∀ a b : Fin n, Tendsto (fun k => iteratedFDeriv ℝ r
      (fun y => (gseq k).inner y (EuclideanSpace.basisFun (Fin n) ℝ a)
        (EuclideanSpace.basisFun (Fin n) ℝ b)) (pseq k)) atTop
      (𝓝 (iteratedFDeriv ℝ r (fun y => g.inner y (EuclideanSpace.basisFun (Fin n) ℝ a)
        (EuclideanSpace.basisFun (Fin n) ℝ b)) p))) :
    Tendsto (fun k => iteratedFDeriv ℝ r (gseq k).euclideanCoefficients (pseq k)) atTop
      (𝓝 (iteratedFDeriv ℝ r g.euclideanCoefficients p)) := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let G := E n →L[ℝ] E n →L[ℝ] ℝ
  let ev (i j : Fin n) : G →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ (b j)).comp
      (ContinuousLinearMap.apply ℝ (E n →L[ℝ] ℝ) (b i))
  let L : (E n [×r]→L[ℝ] G) →ₗ[ℝ] (Fin n → Fin n → E n [×r]→L[ℝ] ℝ) :=
    LinearMap.pi fun i => LinearMap.pi fun j =>
      (ContinuousLinearMap.compContinuousMultilinearMapL ℝ
        (fun _ : Fin r => E n) G ℝ (ev i j)).toLinearMap
  have hL : Function.Injective L := by
    intro A B hAB
    apply ContinuousMultilinearMap.ext
    intro v
    apply ContinuousLinearMap.coe_injective
    apply b.toBasis.ext
    intro i
    apply ContinuousLinearMap.coe_injective
    apply b.toBasis.ext
    intro j
    exact congrArg (fun f => f i j v) hAB
  let : FiniteDimensional ℝ (E n [×r]→L[ℝ] G) :=
    FiniteDimensional.of_injective ContinuousMultilinearMap.toMultilinearMapLinear
      ContinuousMultilinearMap.toMultilinearMap_injective
  have hemb := L.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hL)
  apply hemb.isInducing.tendsto_nhds_iff.mpr
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have heq (g' : RiemannianMetric n (E n)) (x : E n) :
      L (iteratedFDeriv ℝ r g'.euclideanCoefficients x) i j =
        iteratedFDeriv ℝ r (fun y => g'.inner y (b i) (b j)) x := by
    ext v
    exact (g'.iteratedFDeriv_inner_eq x (b i) (b j) r v).symm
  simpa only [Function.comp_apply, heq] using hjet i j

private theorem koszul_smooth {n : ℕ} (u v : E n) :
    ContDiff ℝ ∞ (fun B : E n →L[ℝ] E n →L[ℝ] E n →L[ℝ] ℝ =>
      metricKoszulCovector B u v) := by
  have hf : ContDiff ℝ ∞ (fun B : E n →L[ℝ] E n →L[ℝ] ℝ => B.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ (E n) (E n) ℝ).contDiff
  have hf' : ContDiff ℝ ∞ (fun B : E n →L[ℝ] E n →L[ℝ] E n →L[ℝ] ℝ => B.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ (E n) (E n) (E n →L[ℝ] ℝ)).contDiff
  unfold metricKoszulCovector
  fun_prop

theorem euclideanConnection_jets_tendsto_of_metric_jets {n : ℕ}
    {gseq : ℕ → RiemannianMetric n (E n)} {g : RiemannianMetric n (E n)}
    (Dseq : ∀ k, LeviCivitaData (gseq k)) (D : LeviCivitaData g)
    (pseq : ℕ → E n) (p u v : E n) (r : ℕ)
    (hjet : ∀ m ≤ r + 1, Tendsto
      (fun k => iteratedFDeriv ℝ m (gseq k).euclideanCoefficients (pseq k)) atTop
      (𝓝 (iteratedFDeriv ℝ m g.euclideanCoefficients p))) :
    Tendsto (fun k => iteratedFDeriv ℝ r ((Dseq k).euclideanConnection u v) (pseq k))
      atTop (𝓝 (iteratedFDeriv ℝ r (D.euclideanConnection u v) p)) := by
  let G := E n →L[ℝ] E n →L[ℝ] ℝ
  let Phi : G × (E n →L[ℝ] G) → E n := fun z =>
    z.1.inverse (metricKoszulCovector z.2 u v)
  let jet (g' : RiemannianMetric n (E n)) (y : E n) :=
    (g'.euclideanCoefficients y, fderiv ℝ g'.euclideanCoefficients y)
  have hjetSmooth (g' : RiemannianMetric n (E n)) (y : E n) :
      ContDiffAt ℝ ∞ (jet g') y :=
    (g'.contDiffAt_euclideanCoefficients y).prodMk
      ((g'.contDiffAt_euclideanCoefficients y).fderiv_right (by simp))
  have hPhi (g' : RiemannianMetric n (E n)) (y : E n) :
      ContDiffAt ℝ ∞ Phi (jet g' y) := by
    have hi : (g'.euclideanCoefficients y).IsInvertible := by
      convert! g'.inner_isInvertible y
    have hI := hi.contDiffAt_map_inverse (n := ∞) |>.comp (jet g' y) contDiffAt_fst
    exact hI.clm_apply ((koszul_smooth u v).contDiffAt.comp _ contDiffAt_snd)
  have hderiv (m : ℕ) (hm : m ≤ r) :
      Tendsto (fun k => iteratedFDeriv ℝ m (fderiv ℝ (gseq k).euclideanCoefficients)
        (pseq k)) atTop (𝓝 (iteratedFDeriv ℝ m (fderiv ℝ g.euclideanCoefficients) p)) := by
    let C := continuousMultilinearCurryRightEquiv' ℝ m (E n) G
    have heq (f : E n → G) (y : E n) :
        iteratedFDeriv ℝ m (fderiv ℝ f) y = C (iteratedFDeriv ℝ (m + 1) f y) := by
      rw [iteratedFDeriv_succ_eq_comp_right]
      exact (C.apply_symm_apply _).symm
    simp_rw [heq]
    exact (C.continuous.tendsto _).comp (hjet (m + 1) (by omega))
  have hpairs (m : ℕ) (hm : m ≤ r) := tendsto_iteratedFDeriv_prodMk_of_jets m
    (g.contDiffAt_euclideanCoefficients p)
    ((g.contDiffAt_euclideanCoefficients p).fderiv_right (by simp))
    (Eventually.of_forall fun k => (gseq k).contDiffAt_euclideanCoefficients (pseq k))
    (Eventually.of_forall fun k =>
      ((gseq k).contDiffAt_euclideanCoefficients (pseq k)).fderiv_right (by simp))
    (hjet m (by omega)) (hderiv m hm)
  have h := tendsto_iteratedFDeriv_smooth_comp_of_jets r (hjetSmooth g p)
    (fun k => hjetSmooth (gseq k) (pseq k)) (hPhi g p)
    (fun k => hPhi (gseq k) (pseq k)) hpairs
  have heq (g' : RiemannianMetric n (E n)) (D' : LeviCivitaData g') :
      Phi ∘ jet g' = D'.euclideanConnection u v :=
    funext fun y => (D'.connection_const_eq_inverse y u v).symm
  rw [heq g D] at h
  exact h.congr' (Eventually.of_forall fun k =>
    congrArg (fun f => iteratedFDeriv ℝ r f (pseq k)) (heq (gseq k) (Dseq k)))

end PoincareConjecture.M35
