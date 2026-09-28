import PoincareConjecture.Proofs.M65.Mathlib.Plateau.BeltramiSobolev
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum











set_option autoImplicit false

noncomputable section

open MeasureTheory FourierTransform Filter LineDeriv
open scoped Topology SchwartzMap ContDiff ComplexConjugate LineDeriv

namespace Complex

private theorem smooth_summable_neumann (μ : 𝓢(ℂ, ℂ))
    (hμ : HasCompactSupport (μ : ℂ → ℂ)) {k : ℝ} (hk : k < 1)
    (hbound : ∀ z, ‖μ z‖ ≤ k) (a : 𝓢(ℂ, ℂ)) :
    ContDiff ℝ ∞ (fun z => ∑' n, beltramiNeumannTerm μ hμ a n z) ∧
      (∀ z, Summable (fun n => beltramiNeumannTerm μ hμ a n z)) ∧
      Summable (fun n => ‖(beltramiNeumannTerm μ hμ a n).toLp 2 volume‖) := by
  classical
  obtain ⟨r, hr0, hr1, hbudgets⟩ :=
    exists_geometric_beltramiNeumann_derivative_bounds μ hμ hk hbound a
  choose A _ hA using hbudgets
  choose C hC hSob using exists_norm_iteratedFDeriv_le_planeDerivativeL2Budget
  let v : ℕ → ℕ → ℝ := fun j n => C j * A (2 * (j + 1)) * r ^ n
  have hgeom : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_lt_one hr0.le hr1
  have hv (j : ℕ) : Summable (v j) := hgeom.mul_left _
  have hderiv (j n : ℕ) (z : ℂ) :
      ‖iteratedFDeriv ℝ j (beltramiNeumannTerm μ hμ a n : ℂ → ℂ) z‖ ≤ v j n := by
    calc
      _ ≤ C j * planeDerivativeL2Budget (2 * (j + 1))
          (beltramiNeumannTerm μ hμ a n) := hSob j _ z
      _ ≤ C j * (A (2 * (j + 1)) * r ^ n) :=
        mul_le_mul_of_nonneg_left (hA _ n) (hC j)
      _ = _ := by dsimp [v]; ring
  refine ⟨contDiff_tsum (fun n => (beltramiNeumannTerm μ hμ a n).smooth ⊤)
    (fun j _ => hv j) (fun j n z _ => hderiv j n z), fun z => ?_, ?_⟩
  · apply (hv 0).of_norm_bounded
    intro n
    simpa only [norm_iteratedFDeriv_zero] using hderiv 0 n z
  · apply (hgeom.mul_left (A 0)).of_norm_bounded
    intro n
    simpa only [Real.norm_of_nonneg (norm_nonneg _), planeDerivativeL2Budget] using hA 0 n

private theorem compactSupport_neumann_sum (μ a : 𝓢(ℂ, ℂ))
    (hμ : HasCompactSupport (μ : ℂ → ℂ)) (ha : HasCompactSupport (a : ℂ → ℂ)) :
    HasCompactSupport (fun z => ∑' n, beltramiNeumannTerm μ hμ a n z) := by
  apply (hμ.union ha).of_isClosed_subset isClosed_closure
  apply closure_minimal _ ((isClosed_tsupport _).union (isClosed_tsupport _))
  intro z hz
  by_contra hzK
  have hμz : μ z = 0 := image_eq_zero_of_notMem_tsupport (fun hz => hzK (.inl hz))
  have haz : a z = 0 := image_eq_zero_of_notMem_tsupport (fun hz => hzK (.inr hz))
  apply hz
  have hzero (n : ℕ) : beltramiNeumannTerm μ hμ a n z = 0 := by
    cases n with
    | zero => exact haz
    | succ n => simp only [beltramiNeumannTerm, localizedBeurling_apply, hμz, zero_mul]
  simp only [hzero, tsum_zero]

private theorem toLp_eq_neumann_sum (μ a h : 𝓢(ℂ, ℂ))
    (hμ : HasCompactSupport (μ : ℂ → ℂ))
    (heq : ∀ z, h z = ∑' n, beltramiNeumannTerm μ hμ a n z)
    (hsum : Summable (fun n => ‖(beltramiNeumannTerm μ hμ a n).toLp 2 volume‖)) :
    h.toLp 2 volume = ∑' n, (beltramiNeumannTerm μ hμ a n).toLp 2 volume := by
  apply Lp.ext
  have hterms : ∀ᵐ z ∂volume, ∀ n : ℕ,
      (beltramiNeumannTerm μ hμ a n).toLp 2 volume z = beltramiNeumannTerm μ hμ a n z :=
    ae_all_iff.mpr (fun n => (beltramiNeumannTerm μ hμ a n).coeFn_toLp 2 volume)
  filter_upwards [h.coeFn_toLp 2 volume,
    Lp.coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hsum), hterms] with z hz hsz htz
  rw [hz, hsz, heq z]
  exact tsum_congr (fun n => (htz n).symm)

private theorem beurling_eq_neumann_sum_ae (μ a h : 𝓢(ℂ, ℂ))
    (hμ : HasCompactSupport (μ : ℂ → ℂ))
    (heq : h.toLp 2 volume = ∑' n, (beltramiNeumannTerm μ hμ a n).toLp 2 volume)
    (hsum : Summable (fun n => ‖(beltramiNeumannTerm μ hμ a n).toLp 2 volume‖)) :
    beurlingSchwartz h =ᵐ[volume]
      fun z => ∑' n, beurlingSchwartz (beltramiNeumannTerm μ hμ a n) z := by
  have hBsum : Summable (fun n =>
      ‖beurlingL2 ((beltramiNeumannTerm μ hμ a n).toLp 2 volume)‖) :=
    hsum.of_norm_bounded (fun n => by
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact norm_beurlingL2_le _)
  have hBeq : beurlingL2 (h.toLp 2 volume) =
      ∑' n, beurlingL2 ((beltramiNeumannTerm μ hμ a n).toLp 2 volume) := by
    rw [heq, beurlingL2.map_tsum hsum.of_norm]
  have hterms : ∀ᵐ z ∂volume, ∀ n : ℕ,
      beurlingSchwartz (beltramiNeumannTerm μ hμ a n) z =
        beurlingL2 ((beltramiNeumannTerm μ hμ a n).toLp 2 volume) z :=
    ae_all_iff.mpr (fun n => beurlingSchwartz_ae (beltramiNeumannTerm μ hμ a n))
  filter_upwards [beurlingSchwartz_ae h,
    Lp.coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hBsum), hterms] with z hz hsz htz
  rw [hz, hBeq, hsz]
  exact tsum_congr (fun n => (htz n).symm)







theorem exists_schwartz_beltrami_forcing (μ : 𝓢(ℂ, ℂ))
    (hμ : HasCompactSupport (μ : ℂ → ℂ)) {k : ℝ} (hk : k < 1)
    (hbound : ∀ z, ‖μ z‖ ≤ k) (a : 𝓢(ℂ, ℂ))
    (ha : HasCompactSupport (a : ℂ → ℂ)) :
    ∃ h : 𝓢(ℂ, ℂ), HasCompactSupport (h : ℂ → ℂ) ∧
      ∀ z, h z = μ z * beurlingSchwartz h z + a z := by
  obtain ⟨hsmooth, hpoint, hsum⟩ := smooth_summable_neumann μ hμ hk hbound a
  have hcompact := compactSupport_neumann_sum μ a hμ ha
  let h : 𝓢(ℂ, ℂ) := hcompact.toSchwartzMap hsmooth
  have heq (z : ℂ) : h z = ∑' n, beltramiNeumannTerm μ hμ a n z := rfl
  have hLp := toLp_eq_neumann_sum μ a h hμ heq hsum
  have hB := beurling_eq_neumann_sum_ae μ a h hμ hLp hsum
  have hae : (h : ℂ → ℂ) =ᵐ[volume] fun z => μ z * beurlingSchwartz h z + a z := by
    filter_upwards [hB] with z hz
    rw [heq z, (hpoint z).tsum_eq_zero_add, hz, ← tsum_mul_left]
    change a z + (∑' n, μ z * beurlingSchwartz (beltramiNeumannTerm μ hμ a n) z) = _
    exact add_comm _ _
  have hevery := Measure.eq_of_ae_eq hae h.continuous
    ((μ.continuous.mul (contDiff_beurlingSchwartz h).continuous).add a.continuous)
  exact ⟨h, hcompact, fun z => congrFun hevery z⟩

end Complex
