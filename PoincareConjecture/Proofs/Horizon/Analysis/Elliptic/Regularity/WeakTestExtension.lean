import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.L2Pairing
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Weak.Approximation

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal
open Poincare.Analysis.Sobolev.Weak

namespace Poincare.Analysis.Elliptic

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem weakEquation_of_memW01p
    {O : Set E} (hO : IsOpen O) {F : Fin d → E → ℝ} {f v : E → ℝ}
    {q : Fin d → E → ℝ}
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict O))
    (hf : MemLp f 2 (volume.restrict O))
    (heq : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ O →
      (∫ x in O, ∑ i, F i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x in O, f x * φ x)
    (hv : MemW01p 2 v O)
    (hq : ∀ i, MemLp (q i) 2 (volume.restrict O))
    (hwq : ∀ i, HasWeakPartialDeriv i (q i) v O) :
    (∫ x in O, ∑ i, F i x * q i x) = ∫ x in O, f x * v x := by
  rcases hv with ⟨hv, w, φ, hφ, hφc, hφO, hφlim, hgradlim⟩
  have hqeq (i : Fin d) : (fun x => w.weakGrad x i) =ᵐ[volume.restrict O] q i :=
    (w.isWeakGrad i).ae_eq hO (hwq i)
      ((w.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
      ((hq i).locallyIntegrable (by norm_num))
  have hφLp (n : ℕ) : MemLp (φ n) 2 (volume.restrict O) :=
    ((hφ n).continuous.memLp_of_hasCompactSupport (hφc n)).restrict O
  have hdφLp (n : ℕ) (i : Fin d) :
      MemLp (fun x => fderiv ℝ (φ n) x (EuclideanSpace.single i 1))
        2 (volume.restrict O) := by
    have hdφ := ((hφ n).fderiv_right (m := (⊤ : ℕ∞)) (by norm_cast)).clm_apply
      (contDiff_const (c := EuclideanSpace.single i (1 : ℝ)))
    exact (hdφ.continuous.memLp_of_hasCompactSupport
      ((hφc n).fderiv_apply (𝕜 := ℝ) _)).restrict O
  have hlim (i : Fin d) : Tendsto
      (fun n => ∫ x in O, F i x * fderiv ℝ (φ n) x (EuclideanSpace.single i 1))
      atTop (𝓝 (∫ x in O, F i x * q i x)) := by
    have ht := tendsto_integral_mul_of_eLpNorm_sub (hF i)
      (w.weakGrad_component_memLp i) (fun n => hdφLp n i) (hgradlim i)
    have he : (∫ x in O, F i x * w.weakGrad x i) = ∫ x in O, F i x * q i x := by
      apply integral_congr_ae
      filter_upwards [hqeq i] with x hx
      rw [hx]
    rwa [he] at ht
  have hleft : Tendsto
      (fun n => ∫ x in O, ∑ i, F i x * fderiv ℝ (φ n) x (EuclideanSpace.single i 1))
      atTop (𝓝 (∫ x in O, ∑ i, F i x * q i x)) := by
    have hsumq : (∫ x in O, ∑ i, F i x * q i x) =
        ∑ i, ∫ x in O, F i x * q i x := by
      simpa using integral_finsetSum Finset.univ
        (fun i _ => (hF i).integrable_mul (hq i))
    rw [hsumq]
    convert tendsto_finsetSum Finset.univ (fun i _ => hlim i) using 1
    ext n
    simpa using integral_finsetSum Finset.univ
      (fun i _ => (hF i).integrable_mul (hdφLp n i))
  have hright := tendsto_integral_mul_of_eLpNorm_sub hf hv.1 hφLp hφlim
  exact tendsto_nhds_unique hleft (by
    simpa only [heq _ (hφ _) (hφc _) (hφO _)] using hright)

theorem weakEquation_of_compact_memW1p
    {O : Set E} (hO : IsOpen O) {F : Fin d → E → ℝ} {f v : E → ℝ}
    {q : Fin d → E → ℝ}
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict O))
    (hf : MemLp f 2 (volume.restrict O))
    (heq : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ O →
      (∫ x in O, ∑ i, F i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x in O, f x * φ x)
    (hv : MemLp v 2 (volume.restrict O))
    (hq : ∀ i, MemLp (q i) 2 (volume.restrict O))
    (hwq : ∀ i, HasWeakPartialDeriv i (q i) v O)
    (hvc : HasCompactSupport v) (hvO : tsupport v ⊆ O) :
    (∫ x in O, ∑ i, F i x * q i x) = ∫ x in O, f x * v x := by
  have hv1 : MemW1p 2 v O := ⟨hv, fun i => ⟨q i, hq i, hwq i⟩⟩
  have hv0 : MemW01p 2 v O := by
    simpa using memW01p_of_memW1p_of_tsupport_subset hO
      (p := (2 : ℝ)) (by norm_num) (by simpa using hv1) hvc hvO
  exact weakEquation_of_memW01p hO hF hf heq hv0 hq hwq

end Poincare.Analysis.Elliptic
