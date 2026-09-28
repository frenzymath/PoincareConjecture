import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.ComparisonTest









noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal BigOperators
open Poincare.Analysis.Sobolev.Weak

namespace Poincare.Analysis.Elliptic

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem memLp_top_difference_weight
    {O : Set E} (hO : IsOpen O) {u v : E → ℝ} {A B ε : ℝ≥0}
    (hu : LipschitzOnWith A u O) (hv : LipschitzOnWith B v O)
    (herr : ∀ x ∈ O, |u x - v x| ≤ ε) :
    MemLp (fun x => v x - u x + ε) ∞ (volume.restrict O) := by
  apply memLp_top_of_bound
    (((hv.continuousOn.sub hu.continuousOn).add continuousOn_const).aestronglyMeasurable
      hO.measurableSet) (2 * (ε : ℝ))
  filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [Real.norm_eq_abs]
  have h := abs_le.mp (herr x hx)
  apply abs_le.mpr
  constructor <;> linarith [ε.coe_nonneg]



theorem weak_flux_comparison_energy_le
    {O : Set E} (hO : IsOpen O) {F G : Fin d → E → ℝ} {f g u v φ : E → ℝ}
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict O))
    (hG : ∀ i, MemLp (G i) 2 (volume.restrict O))
    (hf : MemLp f 2 (volume.restrict O)) (hg : MemLp g 2 (volume.restrict O))
    (hleF : ∀ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ O → (∀ x, 0 ≤ ψ x) →
      (∫ x in O, ∑ i, F i x * fderiv ℝ ψ x (EuclideanSpace.single i 1)) ≤
        ∫ x in O, f x * ψ x)
    (hleG : ∀ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ O → (∀ x, 0 ≤ ψ x) →
      (∫ x in O, ∑ i, G i x * fderiv ℝ ψ x (EuclideanSpace.single i 1)) ≤
        ∫ x in O, g x * ψ x)
    {A B ε : ℝ≥0} (hu : LipschitzOnWith A u O) (hv : LipschitzOnWith B v O)
    (herr : ∀ x ∈ O, |u x - v x| ≤ ε)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ O) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1) :
    (∫ x in O, φ x * ∑ i, (G i x - F i x) *
      (fderiv ℝ u x (EuclideanSpace.single i 1) - fderiv ℝ v x (EuclideanSpace.single i 1))) ≤
      (∫ x in O, f x * (φ x * (v x - u x + ε))) +
      (∫ x in O, g x * (φ x * (u x - v x + ε))) -
      ∫ x in O, ∑ i, ((v x - u x + ε) * F i x + (u x - v x + ε) * G i x) *
        fderiv ℝ φ x (EuclideanSpace.single i 1) := by
  let du := fun i x => fderiv ℝ u x (EuclideanSpace.single i 1)
  let dv := fun i x => fderiv ℝ v x (EuclideanSpace.single i 1)
  let dφ := fun i x => fderiv ℝ φ x (EuclideanSpace.single i 1)
  let w := fun x => v x - u x + (ε : ℝ)
  let z := fun x => u x - v x + (ε : ℝ)
  have herr' : ∀ x ∈ O, |v x - u x| ≤ ε := by simpa only [abs_sub_comm] using herr
  have hw := memLp_top_difference_weight hO hu hv herr
  have hz := memLp_top_difference_weight hO hv hu herr'
  have hdu (i) : MemLp (du i) ∞ (volume.restrict O) :=
    memLp_top_fderiv_apply_of_lipschitzOn hO hu _
  have hdv (i) : MemLp (dv i) ∞ (volume.restrict O) :=
    memLp_top_fderiv_apply_of_lipschitzOn hO hv _
  have hp : MemLp φ 2 (volume.restrict O) :=
    (hφ.continuous.memLp_of_hasCompactSupport hφc).restrict O
  have hdp (i) : MemLp (dφ i) 2 (volume.restrict O) := by
    have h := (hφ.fderiv_right (m := (⊤ : ℕ∞)) (by norm_cast)).clm_apply
      (contDiff_const (c := EuclideanSpace.single i (1 : ℝ)))
    exact (h.continuous.memLp_of_hasCompactSupport (hφc.fderiv_apply (𝕜 := ℝ) _)).restrict O
  let L₁ := fun x => ∑ i, F i x * (φ x * (dv i x - du i x) + w x * dφ i x)
  let L₂ := fun x => ∑ i, G i x * (φ x * (du i x - dv i x) + z x * dφ i x)
  let energy := fun x => φ x * ∑ i, (G i x - F i x) * (du i x - dv i x)
  let boundary := fun x => ∑ i, (w x * F i x + z x * G i x) * dφ i x
  have hproduct {a b : E → ℝ} (ha : MemLp a ∞ (volume.restrict O))
      (hb : MemLp b 2 (volume.restrict O)) :
      MemLp (fun x => b x * a x) 2 (volume.restrict O) := ha.mul' hb
  have hproduct' {a b : E → ℝ} (ha : MemLp a ∞ (volume.restrict O))
      (hb : MemLp b 2 (volume.restrict O)) :
      MemLp (fun x => a x * b x) 2 (volume.restrict O) := hb.mul' ha
  have hL₁ : IntegrableOn L₁ O := by
    apply integrable_finsetSum
    intro i _
    exact (hF i).integrable_mul
      ((hproduct ((hdv i).sub (hdu i)) hp).add (hproduct' hw (hdp i)))
  have hL₂ : IntegrableOn L₂ O := by
    apply integrable_finsetSum
    intro i _
    exact (hG i).integrable_mul
      ((hproduct ((hdu i).sub (hdv i)) hp).add (hproduct' hz (hdp i)))
  have he : IntegrableOn energy O := by
    have hsum : IntegrableOn
        (fun x => ∑ i, (G i x - F i x) * (φ x * (du i x - dv i x))) O := by
      apply integrable_finsetSum
      intro i _
      exact ((hG i).sub (hF i)).integrable_mul (hproduct ((hdu i).sub (hdv i)) hp)
    convert hsum using 1
    funext x
    dsimp only [energy]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hb : IntegrableOn boundary O := by
    apply integrable_finsetSum
    intro i _
    have h := ((hF i).integrable_mul (hproduct' hw (hdp i))).add
      ((hG i).integrable_mul (hproduct' hz (hdp i)))
    convert h using 1
    funext x
    dsimp only [Pi.add_apply, Pi.mul_apply, w, z]
    ring
  have hidentity : (∫ x in O, energy x) + (∫ x in O, boundary x) =
      (∫ x in O, L₁ x) + ∫ x in O, L₂ x := by
    rw [← integral_add he hb, ← integral_add hL₁ hL₂]
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [energy, boundary, L₁, L₂]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hfirst := weakInequality_comparison_test hO hF hf hleF hu hv herr hφ hφc hφO hφ0 hφ1
  have hsecond := weakInequality_comparison_test hO hG hg hleG hv hu herr' hφ hφc hφO hφ0 hφ1
  change (∫ x in O, energy x) ≤ _ - ∫ x in O, boundary x
  change (∫ x in O, L₁ x) ≤ _ at hfirst
  change (∫ x in O, L₂ x) ≤ _ at hsecond
  linarith

end Poincare.Analysis.Elliptic
