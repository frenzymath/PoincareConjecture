import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.SmoothCurrentCurl
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.CircleTangentConstraint
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.InnerStrongApproximation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRegularityCharts












set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace PoincareConjecture.M64

open Poincare.Analysis.Sobolev.Weak

local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "b" => fun i : Fin 2 => EuclideanSpace.single i (1 : ℝ)

private theorem restrict_supported_test {O K : Set E}
    (hO : MeasurableSet O) (hKO : K ⊆ O)
    {psi : E → ℝ} (hpsi : tsupport psi ⊆ K) (w : E → ℝ) :
    (∫ p in O, psi p * w p) = ∫ p in K, psi p * w p := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hO hKO
  intro p hp
  rw [image_eq_zero_of_notMem_tsupport (fun h => hp.2 (hpsi h)), zero_mul]




theorem weak_planar_current_test_identity
    {O : Set E} (hO : IsOpen O) (u : E → E) (V : Fin 2 → E → E)
    (hu : MemLp u 2 (volume.restrict O))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict O))
    (hw : ∀ i a, HasWeakPartialDeriv i (fun p => V i p a) (fun p => u p a) O)
    (phi : E → ℝ) (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ O) :
    (∫ p in O, fderiv ℝ phi p (b 1) * planarCircleCurrent (u p) (V 0 p)) -
      (∫ p in O, fderiv ℝ phi p (b 0) * planarCircleCurrent (u p) (V 1 p)) =
        2 * ∫ p in O, phi p * planarCircleCurrent (V 0 p) (V 1 p) := by
  let K := tsupport phi
  have hK : IsCompact K := hc
  let mu := volume.restrict K
  obtain ⟨f, hf, hfu, hDV⟩ := m64WeakMap_inner_strong_approximation hO hK hs u V hu hV hw
  let D := fun (j : ℕ) (i : Fin 2) (p : E) => fderiv ℝ (f j) p (b i)
  have hfL (j : ℕ) : MemLp (f j) 2 mu := by
    apply (memLp_two_iff_integrable_sq_norm (hf j).continuous.aestronglyMeasurable).mpr
    exact ((hf j).continuous.norm.pow 2).continuousOn.integrableOn_compact hK
  have hDL (j : ℕ) (i : Fin 2) : MemLp (D j i) 2 mu := by
    have hcont : Continuous (D j i) :=
      ((hf j).continuous_fderiv (by simp)).clm_apply continuous_const
    apply (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mpr
    exact (hcont.norm.pow 2).continuousOn.integrableOn_compact hK
  have huL : MemLp u 2 mu := hu.mono_measure (Measure.restrict_mono hs le_rfl)
  have hVL (i : Fin 2) : MemLp (V i) 2 mu :=
    (hV i).mono_measure (Measure.restrict_mono hs le_rfl)
  have hpL : MemLp phi ∞ mu :=
    hp.continuous.memLp_top_of_hasCompactSupport hc mu
  have hdpL (i : Fin 2) : MemLp (fun p => fderiv ℝ phi p (b i)) ∞ mu := by
    have hcont : Continuous (fun p => fderiv ℝ phi p (b i)) :=
      (hp.continuous_fderiv (by simp)).clm_apply continuous_const
    exact hcont.memLp_top_of_hasCompactSupport (hc.fderiv_apply ℝ (b i)) mu
  have hlim0 := strongSquare_planarCurrent_pairing_tendsto f (fun j => D j 0) u (V 0)
    hfL (fun j => hDL j 0) huL (hVL 0) hfu (hDV 0) _ (hdpL 1)
  have hlim1 := strongSquare_planarCurrent_pairing_tendsto f (fun j => D j 1) u (V 1)
    hfL (fun j => hDL j 1) huL (hVL 1) hfu (hDV 1) _ (hdpL 0)
  have hlimD := strongSquare_planarCurrent_pairing_tendsto (fun j => D j 0)
    (fun j => D j 1) (V 0) (V 1) (fun j => hDL j 0) (fun j => hDL j 1)
    (hVL 0) (hVL 1) (hDV 0) (hDV 1) phi hpL
  have hres {psi : E → ℝ} (hpsi : tsupport psi ⊆ K) (w : E → ℝ) :
      (∫ p in O, psi p * w p) = ∫ p in K, psi p * w p :=
    restrict_supported_test hO.measurableSet hs hpsi w
  have hresD (i : Fin 2) (w : E → ℝ) :
      (∫ p in O, fderiv ℝ phi p (b i) * w p) =
        ∫ p in K, fderiv ℝ phi p (b i) * w p :=
    hres (tsupport_fderiv_apply_subset ℝ (b i)) w
  have heq (j : ℕ) :
      (∫ p in K, fderiv ℝ phi p (b 1) * planarCircleCurrent (f j p) (D j 0 p)) -
        (∫ p in K, fderiv ℝ phi p (b 0) * planarCircleCurrent (f j p) (D j 1 p)) =
          2 * ∫ p in K, phi p * planarCircleCurrent (D j 0 p) (D j 1 p) := by
    have h := smooth_planar_current_test_identity (f j) (hf j) hO phi hp hc hs
    rw [hresD 1, hresD 0, hres (Subset.refl K)] at h
    exact h
  have hlimit := tendsto_nhds_unique (hlim0.sub hlim1)
    ((hlimD.const_mul 2).congr' (Eventually.of_forall (fun j => (heq j).symm)))
  rw [hresD 1, hresD 0, hres (Subset.refl K)]
  exact hlimit

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]




theorem observedWeakAnnulus_circle_current_closed
    (e : M → EuclideanSpace ℝ (Fin m)) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (R : EuclideanSpace ℝ (Fin m) →L[ℝ] E) (hnorm : ∀ q, ‖R (e q)‖ = 1)
    {c0 c1 : ℝ → M} (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (phi : E → ℝ) (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ interior m64AnnulusDomain) :
    (∫ p in interior m64AnnulusDomain, fderiv ℝ phi p (b 1) *
      planarCircleCurrent (R (e (A.map p))) (R (A.column 0 p))) =
    (∫ p in interior m64AnnulusDomain, fderiv ℝ phi p (b 0) *
      planarCircleCurrent (R (e (A.map p))) (R (A.column 1 p))) := by
  have h := weak_planar_current_test_identity isOpen_interior
    (fun p => R (e (A.map p))) (fun i p => R (A.column i p))
    (R.comp_memLp' A.observed_memLp) (fun i => R.comp_memLp' (Lp.memLp (A.column i)))
    (fun i a => m64WeakPartial_comp_linear A.observed_memLp (Lp.memLp (A.column i))
      (A.weak_partial i) R a) phi hp hc hs
  have hz : (∫ p in interior m64AnnulusDomain,
      phi p * planarCircleCurrent (R (A.column 0 p)) (R (A.column 1 p))) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [observedWeakAnnulus_circle_jacobian_zero e he R hnorm A] with p hp
    simp only [hp, mul_zero, Pi.zero_apply]
  rw [hz, mul_zero] at h
  exact sub_eq_zero.mp h

end PoincareConjecture.M64
