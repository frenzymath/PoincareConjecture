import PoincareConjecture.Proofs.M08.SecondVariationCoordinates

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M14

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (q : ℝ × ℝ → E)
  (hq : ContDiffOn ℝ ∞ q Ω) {p : ℝ × ℝ} (hp : p ∈ Ω)
  (Γ : ℝ × E → E →L[ℝ] E →L[ℝ] E)

include hΩ hq hp

theorem coordinateCovariantU_partialU_eq_slice :
    M08.coordinateCovariantU Γ q (M08.coordinatePartialU q) p =
      deriv (deriv (fun v => q (p.1, v))) p.2 +
        Γ (p.1, q p) (deriv (fun v => q (p.1, v)) p.2)
          (deriv (fun v => q (p.1, v)) p.2) := by
  have hqd := (hq.contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp)
  have hY := M08.coordinatePartialU_contDiffOn hΩ q hq
  have hYd := (hY.contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp)
  have hnear : ∀ᶠ v in 𝓝 p.2, (p.1, v) ∈ Ω :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hΩ.mem_nhds hp)
  have heq : (fun v => M08.coordinatePartialU q (p.1, v)) =ᶠ[𝓝 p.2]
      deriv (fun v => q (p.1, v)) := by
    filter_upwards [hnear] with v hv
    exact (M08.coordinateSlice_snd_hasDerivAt q
      ((hq.contDiffAt (hΩ.mem_nhds hv)).differentiableAt (by simp))).deriv.symm
  change fderiv ℝ (M08.coordinatePartialU q) p (0, 1) +
    Γ (p.1, q p) (fderiv ℝ q p (0, 1)) (fderiv ℝ q p (0, 1)) = _
  rw [← (M08.coordinateSlice_snd_hasDerivAt _ hYd).deriv, heq.deriv_eq,
    ← (M08.coordinateSlice_snd_hasDerivAt q hqd).deriv]

theorem coordinateCovariantS_partialU_eq_slice {S : Set ℝ} (hS : S ∈ 𝓝 p.1) :
    M08.coordinateCovariantS Γ q (M08.coordinatePartialU q) p =
      derivWithin (fun r => deriv (fun v => q (r, v)) p.2) S p.1 +
        Γ (p.1, q p) (derivWithin (fun r => q (r, p.2)) S p.1)
          (deriv (fun v => q (p.1, v)) p.2) := by
  have hqd := (hq.contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp)
  have hY := M08.coordinatePartialU_contDiffOn hΩ q hq
  have hYd := (hY.contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp)
  have hnear : ∀ᶠ r in 𝓝 p.1, (r, p.2) ∈ Ω :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hΩ.mem_nhds hp)
  have heq : (fun r => M08.coordinatePartialU q (r, p.2)) =ᶠ[𝓝 p.1]
      (fun r => deriv (fun v => q (r, v)) p.2) := by
    filter_upwards [hnear] with r hr
    exact (M08.coordinateSlice_snd_hasDerivAt q
      ((hq.contDiffAt (hΩ.mem_nhds hr)).differentiableAt (by simp))).deriv.symm
  change fderiv ℝ (M08.coordinatePartialU q) p (1, 0) +
    Γ (p.1, q p) (fderiv ℝ q p (1, 0)) (fderiv ℝ q p (0, 1)) = _
  rw [← (M08.coordinateSlice_fst_hasDerivAt _ hYd).deriv, heq.deriv_eq,
    ← (M08.coordinateSlice_fst_hasDerivAt q hqd).deriv,
    ← (M08.coordinateSlice_snd_hasDerivAt q hqd).deriv,
    derivWithin_of_mem_nhds hS, derivWithin_of_mem_nhds hS]

theorem coordinateCovariantS_partialS_eq_slice {S : Set ℝ} (hS : S ∈ 𝓝 p.1) :
    M08.coordinateCovariantS Γ q (M08.coordinatePartialS q) p =
      derivWithin (derivWithin (fun r => q (r, p.2)) S) S p.1 +
        Γ (p.1, q p) (derivWithin (fun r => q (r, p.2)) S p.1)
          (derivWithin (fun r => q (r, p.2)) S p.1) := by
  have hqd := (hq.contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp)
  have hA := M08.coordinatePartialS_contDiffOn hΩ q hq
  have hAd := (hA.contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp)
  have hnear : ∀ᶠ r in 𝓝 p.1, (r, p.2) ∈ Ω :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hΩ.mem_nhds hp)
  have heq : (fun r => M08.coordinatePartialS q (r, p.2)) =ᶠ[𝓝 p.1]
      derivWithin (fun r => q (r, p.2)) S := by
    filter_upwards [hnear, isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hS)]
      with r hr hrS
    exact (M08.coordinateSlice_fst_hasDerivAt q
      ((hq.contDiffAt (hΩ.mem_nhds hr)).differentiableAt (by simp))).deriv.symm.trans
        (derivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hrS)).symm
  change fderiv ℝ (M08.coordinatePartialS q) p (1, 0) +
    Γ (p.1, q p) (fderiv ℝ q p (1, 0)) (fderiv ℝ q p (1, 0)) = _
  rw [← (M08.coordinateSlice_fst_hasDerivAt _ hAd).deriv, heq.deriv_eq,
    ← (M08.coordinateSlice_fst_hasDerivAt q hqd).deriv,
    derivWithin_of_mem_nhds hS, derivWithin_of_mem_nhds hS]

end PoincareConjecture.M14
