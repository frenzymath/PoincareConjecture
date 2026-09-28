import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.GradientCompactness.Coercivity

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal BigOperators

namespace Poincare.Analysis.Elliptic

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem weak_flux_comparison_energy_le_of_bound
    {O : Set E} (hO : IsOpen O) [IsFiniteMeasure (volume.restrict O)]
    {F G : Fin d → E → ℝ} {f g u v φ : E → ℝ}
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
    (hφO : tsupport φ ⊆ O) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hfC : ∀ x ∈ O, |f x| ≤ C) (hgC : ∀ x ∈ O, |g x| ≤ C)
    (hFC : ∀ i x, x ∈ O → |F i x| ≤ C)
    (hGC : ∀ i x, x ∈ O → |G i x| ≤ C)
    (hdφ : ∀ i x, x ∈ O → |fderiv ℝ φ x (EuclideanSpace.single i 1)| ≤ D) :
    (∫ x in O, φ x * ∑ i, (G i x - F i x) *
      (fderiv ℝ u x (EuclideanSpace.single i 1) -
        fderiv ℝ v x (EuclideanSpace.single i 1))) ≤
      4 * ε * C * (1 + (d : ℝ) * D) * volume.real O := by
  let w := fun x => v x - u x + (ε : ℝ)
  let z := fun x => u x - v x + (ε : ℝ)
  let dp := fun i x => fderiv ℝ φ x (EuclideanSpace.single i 1)
  have hwbound (x) (hx : x ∈ O) : |w x| ≤ 2 * ε := by
    have h := abs_le.mp (herr x hx)
    dsimp only [w]
    exact abs_le.mpr ⟨by linarith [ε.coe_nonneg], by linarith⟩
  have hzbound (x) (hx : x ∈ O) : |z x| ≤ 2 * ε := by
    have h := abs_le.mp (herr x hx)
    dsimp only [z]
    exact abs_le.mpr ⟨by linarith [ε.coe_nonneg], by linarith⟩
  have hw : MemLp w ∞ (volume.restrict O) := by
    apply memLp_top_of_bound
      (((hv.continuousOn.sub hu.continuousOn).add continuousOn_const).aestronglyMeasurable
        hO.measurableSet) (2 * (ε : ℝ))
    filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
    exact (Real.norm_eq_abs _).symm ▸ hwbound x hx
  have hz : MemLp z ∞ (volume.restrict O) := by
    apply memLp_top_of_bound
      (((hu.continuousOn.sub hv.continuousOn).add continuousOn_const).aestronglyMeasurable
        hO.measurableSet) (2 * (ε : ℝ))
    filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
    exact (Real.norm_eq_abs _).symm ▸ hzbound x hx
  have hp : MemLp φ ∞ (volume.restrict O) :=
    (hφ.continuous.memLp_of_hasCompactSupport hφc).restrict O
  have hdp (i) : MemLp (dp i) ∞ (volume.restrict O) := by
    have h := (hφ.fderiv_right (m := (⊤ : ℕ∞)) (by norm_cast)).clm_apply
      (contDiff_const (c := EuclideanSpace.single i (1 : ℝ)))
    exact (h.continuous.memLp_of_hasCompactSupport (hφc.fderiv_apply (𝕜 := ℝ) _)).restrict O
  let R₁ := fun x => f x * (φ x * w x)
  let R₂ := fun x => g x * (φ x * z x)
  let bd := fun x => ∑ i, (w x * F i x + z x * G i x) * dp i x
  have hwp : MemLp (fun x => φ x * w x) ∞ (volume.restrict O) := hw.mul' hp
  have hzp : MemLp (fun x => φ x * z x) ∞ (volume.restrict O) := hz.mul' hp
  have hR₁ : MemLp R₁ 2 (volume.restrict O) := hwp.mul' hf
  have hR₂ : MemLp R₂ 2 (volume.restrict O) := hzp.mul' hg
  have hbd : MemLp bd 2 (volume.restrict O) := by
    apply memLp_finsetSum
    intro i _
    have hfirst : MemLp (fun x => w x * F i x) 2 (volume.restrict O) := (hF i).mul' hw
    have hsecond : MemLp (fun x => z x * G i x) 2 (volume.restrict O) := (hG i).mul' hz
    exact (hdp i).mul' (hfirst.add hsecond)
  have hR := (hR₁.add hR₂).sub hbd
  have hbound : (∫ x in O, R₁ x + R₂ x - bd x) ≤
      4 * ε * C * (1 + (d : ℝ) * D) * volume.real O := by
    have h := integral_mono_ae (hR.integrable (by norm_num))
      (integrable_const (4 * (ε : ℝ) * C * (1 + (d : ℝ) * D))) ?_
    · simpa only [Pi.sub_apply, Pi.add_apply, integral_const, smul_eq_mul, measureReal_restrict_apply_univ,
        mul_comm] using h
    · filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
      exact flux_comparison_remainder_le ε.coe_nonneg hC hD
        (hfC x hx) (hgC x hx) (fun i => hFC i x hx) (fun i => hGC i x hx)
        (fun i => hdφ i x hx) (by rw [abs_of_nonneg (hφ0 x)]; exact hφ1 x)
        (hwbound x hx) (hzbound x hx)
  have hflux := weak_flux_comparison_energy_le hO hF hG hf hg hleF hleG
    hu hv herr hφ hφc hφO hφ0 hφ1
  change _ ≤ (∫ x in O, R₁ x) + (∫ x in O, R₂ x) - ∫ x in O, bd x at hflux
  have hsum : IntegrableOn (fun x => R₁ x + R₂ x) O :=
    (hR₁.integrable (by norm_num)).add (hR₂.integrable (by norm_num))
  rw [integral_sub hsum (hbd.integrable (by norm_num)),
    integral_add (hR₁.integrable (by norm_num)) (hR₂.integrable (by norm_num))] at hbound
  exact hflux.trans hbound

end Poincare.Analysis.Elliptic
