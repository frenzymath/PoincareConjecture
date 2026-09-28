import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Iterated.Multiply








noncomputable section

open Set MeasureTheory Function Filter Topology
open scoped ENNReal ContDiff

namespace Poincare.Analysis.Elliptic.Iteration

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)


def partialDeriv (i : Fin n) (f : E → ℝ) : E → ℝ :=
  fun x => (fderiv ℝ f x) (EuclideanSpace.single i 1)

theorem contDiff_partial {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin n) :
    ContDiff ℝ ∞ (partialDeriv i f) :=
  Sobolev.Euclidean.contDiff_partial_eta hf i

theorem hasCompactSupport_partial {f : E → ℝ} (hf : HasCompactSupport f) (i : Fin n) :
    HasCompactSupport (partialDeriv i f) := hf.fderiv_apply (𝕜 := ℝ) _

theorem tsupport_partial_subset (i : Fin n) (f : E → ℝ) :
    tsupport (partialDeriv i f) ⊆ tsupport f :=
  tsupport_fderiv_apply_subset ℝ _

theorem partial_comm {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (i j : Fin n) :
    partialDeriv i (partialDeriv j f) = partialDeriv j (partialDeriv i f) := by
  funext x
  have hfd : Differentiable ℝ (fderiv ℝ f) :=
    ((contDiff_infty_iff_fderiv.1 hf).2).differentiable (by simp)
  have hflip : ∀ k : Fin n, fderiv ℝ (partialDeriv k f) x =
      (fderiv ℝ (fderiv ℝ f) x).flip (EuclideanSpace.single k 1) := by
    intro k
    unfold partialDeriv
    rw [fderiv_clm_apply (hfd x) (differentiableAt_const _)]
    simp
  have hsymm : IsSymmSndFDerivAt ℝ f x :=
    hf.contDiffAt.isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField]
      decide)
  change (fderiv ℝ (partialDeriv j f) x) (EuclideanSpace.single i 1) =
    (fderiv ℝ (partialDeriv i f) x) (EuclideanSpace.single j 1)
  rw [hflip j, hflip i]
  exact hsymm _ _

theorem integrable_mul_test {O : Set E} {f φ : E → ℝ}
    (hf : LocallyIntegrable f (volume.restrict O))
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    Integrable (fun x => f x * φ x) (volume.restrict O) := by
  simpa only [smul_eq_mul] using
    hf.integrable_smul_right_of_hasCompactSupport hφ.continuous hφc

theorem integrable_mul_partial_test {O : Set E} {f φ : E → ℝ}
    (hf : LocallyIntegrable f (volume.restrict O))
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (i : Fin n) :
    Integrable (fun x => f x * partialDeriv i φ x) (volume.restrict O) :=
  integrable_mul_test hf (contDiff_partial hφ i) (hasCompactSupport_partial hφc i)


theorem weakPartial_comm_ae
    {O : Set E} (hO : IsOpen O) {u p q r s : E → ℝ} {i j : Fin n}
    (hp : Sobolev.Weak.HasWeakPartialDeriv i p u O)
    (hq : Sobolev.Weak.HasWeakPartialDeriv j q u O)
    (hr : Sobolev.Weak.HasWeakPartialDeriv j r p O)
    (hs : Sobolev.Weak.HasWeakPartialDeriv i s q O)
    (hrint : LocallyIntegrable r (volume.restrict O))
    (hsint : LocallyIntegrable s (volume.restrict O)) :
    r =ᵐ[volume.restrict O] s := by
  suffices h : (fun x => r x - s x) =ᵐ[volume.restrict O] 0 by
    filter_upwards [h] with x hx
    exact sub_eq_zero.mp hx
  change ∀ᵐ x ∂volume.restrict O, r x - s x = 0
  rw [ae_restrict_iff' hO.measurableSet]
  apply hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (locallyIntegrableOn_of_locallyIntegrable_restrict (hrint.sub hsint))
  intro φ hφ hφc hφO
  have hp' := hp (partialDeriv j φ) (contDiff_partial hφ j)
    (hasCompactSupport_partial hφc j) ((tsupport_partial_subset j φ).trans hφO)
  have hq' := hq (partialDeriv i φ) (contDiff_partial hφ i)
    (hasCompactSupport_partial hφc i) ((tsupport_partial_subset i φ).trans hφO)
  have hr' := hr φ hφ hφc hφO
  have hs' := hs φ hφ hφc hφO
  change (∫ x in O, u x * partialDeriv i (partialDeriv j φ) x) =
    -(∫ x in O, p x * partialDeriv j φ x) at hp'
  change (∫ x in O, u x * partialDeriv j (partialDeriv i φ) x) =
    -(∫ x in O, q x * partialDeriv i φ x) at hq'
  rw [partial_comm hφ i j] at hp'
  change (∫ x in O, p x * partialDeriv j φ x) = -(∫ x in O, r x * φ x) at hr'
  change (∫ x in O, q x * partialDeriv i φ x) = -(∫ x in O, s x * φ x) at hs'
  have heq : (∫ x in O, r x * φ x) = ∫ x in O, s x * φ x := by linarith
  have hzero : ∀ x, x ∉ O → φ x • (r - s) x = 0 := by
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport (fun h => hx (hφO h))]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  simp only [Pi.sub_apply, smul_eq_mul, mul_sub]
  have hrφ := integrable_mul_test hrint hφ hφc
  have hsφ := integrable_mul_test hsint hφ hφc
  simp_rw [mul_comm (φ _)]
  rw [integral_sub hrφ hsφ, heq, sub_self]

end Poincare.Analysis.Elliptic.Iteration
