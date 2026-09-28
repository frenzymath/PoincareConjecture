import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.WeakCurrentCurl
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerWeakAverages

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology Manifold ContDiff Convolution ENNReal

namespace PoincareConjecture.M64

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "b" => fun i : Fin 2 => EuclideanSpace.single i (1 : ℝ)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

theorem closed_current_convolution_closed
    {O : Set Plane} (hO : MeasurableSet O) (J : Fin 2 → Plane → ℝ)
    (hJ : ∀ i, LocallyIntegrable (O.indicator (J i)) volume)
    (hclosed : ∀ (psi : Plane → ℝ), ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ O →
      (∫ p in O, fderiv ℝ psi p (b 1) * J 0 p) =
        ∫ p in O, fderiv ℝ psi p (b 0) * J 1 p)
    {phi : Plane → ℝ} (hphi : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (x : Plane) (hs : tsupport (fun y => phi (x - y)) ⊆ O) :
    fderiv ℝ (phi ⋆[lsmul ℝ ℝ, volume] O.indicator (J 0)) x (b 1) =
      fderiv ℝ (phi ⋆[lsmul ℝ ℝ, volume] O.indicator (J 1)) x (b 0) := by
  classical
  let psi : Plane → ℝ := fun y => phi (x - y)
  let T : Plane ≃ₜ Plane := (Homeomorph.neg Plane).trans (Homeomorph.addLeft x)
  have hp : ContDiff ℝ ∞ psi := hphi.comp (contDiff_const.sub contDiff_id)
  have hpc : HasCompactSupport psi := by
    simpa [psi, T, Function.comp_def, sub_eq_add_neg] using hc.comp_homeomorph T
  have hd (i : Fin 2) (y : Plane) : fderiv ℝ psi y (b i) =
      -fderiv ℝ phi (x - y) (b i) := by
    have h := (hphi.differentiable (by simp) (x - y)).hasFDerivAt.comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    change HasFDerivAt psi _ y at h
    rw [h.fderiv]
    simp
  have ht := hclosed psi hp hpc hs
  simp_rw [hd, neg_mul] at ht
  rw [integral_neg, integral_neg] at ht
  have heq := neg_injective ht
  have hind (v k : Plane → ℝ) :
      (∫ y, k y * O.indicator v y) = ∫ y in O, k y * v y := by
    rw [← integral_indicator hO]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by by_cases hy : y ∈ O <;> simp [hy]
  rw [M60.suConvolution_fderiv_apply hphi hc (hJ 0),
    M60.suConvolution_fderiv_apply hphi hc (hJ 1),
    convolution_lsmul_swap, convolution_lsmul_swap]
  simp only [smul_eq_mul]
  rw [hind, hind]
  exact heq

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin m)

theorem observedWeakAnnulus_circle_current_memLp
    (e : M → E) (R : E →L[ℝ] Plane) (hnorm : ∀ q, ‖R (e q)‖ = 1)
    {c0 c1 : ℝ → M} (A : M64ObservedWeakAnnulus (n := n) e c0 c1) (i : Fin 2) :
    MemLp (fun p => planarCircleCurrent (R (e (A.map p))) (R (A.column i p))) 2 mu := by
  have hu : MemLp (fun p => R (e (A.map p))) ∞ mu :=
    memLp_top_of_bound (R.comp_memLp' A.observed_memLp).aestronglyMeasurable 1
      (Eventually.of_forall fun p => (hnorm (A.map p)).le)
  have hv := R.comp_memLp' (Lp.memLp (A.column i))
  simpa only [planarCurrentBilinear_apply, Function.comp_apply] using
    planarCurrentBilinear.memLp_of_bilin 2 hu hv

theorem observedWeakAnnulus_smoothed_circle_current_closed
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (R : E →L[ℝ] Plane) (hnorm : ∀ q, ‖R (e q)‖ = 1)
    {c0 c1 : ℝ → M} (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    {phi : Plane → ℝ} (hphi : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (x : Plane) (hs : tsupport (fun y => phi (x - y)) ⊆ S) :
    fderiv ℝ (phi ⋆[lsmul ℝ ℝ, volume] (S).indicator
      (fun p => planarCircleCurrent (R (e (A.map p))) (R (A.column 0 p)))) x (b 1) =
    fderiv ℝ (phi ⋆[lsmul ℝ ℝ, volume] (S).indicator
      (fun p => planarCircleCurrent (R (e (A.map p))) (R (A.column 1 p)))) x (b 0) := by
  apply closed_current_convolution_closed isOpen_interior.measurableSet
    (fun i p => planarCircleCurrent (R (e (A.map p))) (R (A.column i p)))
  · intro i
    exact ((memLp_indicator_iff_restrict isOpen_interior.measurableSet).mpr
      (observedWeakAnnulus_circle_current_memLp e R hnorm A i)).locallyIntegrable (by norm_num)
  · exact observedWeakAnnulus_circle_current_closed e he R hnorm A
  · exact hphi
  · exact hc
  · exact hs

end PoincareConjecture.M64
