import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Operators.Powers
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Operators.Localization
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Embedding.Compact













noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace Poincare.Analysis.Elliptic.InteriorEstimates

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)



theorem uniform_interior_estimate_of_elliptic_powers
    {O V K : Set E} (hO : IsOpen O) (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hVO : closure V ⊆ O)
    (hK : IsCompact K) (hKV : K ⊆ V)
    (a : E → Matrix (Fin d) (Fin d) ℝ) (b : Fin d → E → ℝ)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) O)
    (hpos : ∀ x ∈ O, (a x).PosDef)
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) O) (m : ℕ) :
    ∃ q : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ {u : E → ℝ}, ContDiffOn ℝ ∞ u O → ∀ x ∈ K,
      ‖iteratedFDeriv ℝ m u x‖ ≤ C * ∑ j ∈ Finset.range (q + 1),
        (eLpNorm ((secondOrderOperator a b)^[j] u) 2 (volume.restrict V)).toReal := by
  obtain ⟨B, b', hb', hBa, hb'b⟩ :=
    exists_secondOrderOperator_extension hO hVc hVO a b ha hpos hb
  obtain ⟨W, hW, hKW, hWV⟩ := hK.exists_isOpen_closure_subset (hV.mem_nhdsSet.mpr hKV)
  have hWc : IsCompact (closure W) :=
    hVc.of_isClosed_subset isClosed_closure (hWV.trans subset_closure)
  obtain ⟨A, hA, hjet⟩ := smooth_jet_le_l2_derivativeProfile_on_compact hK hW hWc hKW m
  obtain ⟨D, hD, hpower⟩ := exists_derivativeProfile_le_ellipticPowerProfile
    B b' hb' (m + 1 + d) hV hVc (subset_univ _) hW hWc hWV
  refine ⟨m + 1 + d, A * (D + 1), mul_pos hA (by positivity), ?_⟩
  intro u hu x hx
  obtain ⟨v, hv, hvu⟩ := exists_smooth_extension_on_precompact hO hVc hVO hu
  have heq (j : ℕ) : ((secondOrderOperator B.a b')^[j] v) =ᵐ[volume.restrict V]
      ((secondOrderOperator a b)^[j] u) := by
    filter_upwards [ae_restrict_mem hV.measurableSet] with y hy
    exact iterate_secondOrderOperator_eqOn hV hBa hb'b hvu j hy
  have hfinite (j : ℕ) :
      eLpNorm ((secondOrderOperator B.a b')^[j] v) 2 (volume.restrict V) ≠ ⊤ :=
    ((continuous_memLp_on_compact
      (contDiff_iterate_secondOrderOperator B.smooth_a hb' hv j).continuous hVc).mono_measure
        (Measure.restrict_mono subset_closure le_rfl)).eLpNorm_ne_top
  have hsum : (ellipticPowerProfile B.a b' V (m + 1 + d) v).toReal =
      ∑ j ∈ Finset.range (m + 1 + d + 1),
        (eLpNorm ((secondOrderOperator a b)^[j] u) 2 (volume.restrict V)).toReal := by
    unfold ellipticPowerProfile
    simp only [derivativeProfile_zero]
    rw [ENNReal.toReal_sum (fun j _ => hfinite j)]
    exact Finset.sum_congr rfl (fun j _ => congrArg ENNReal.toReal (eLpNorm_congr_ae (heq j)))
  have hprofile : (derivativeProfile 2 W (m + 1 + d) v).toReal ≤
      D * (ellipticPowerProfile B.a b' V (m + 1 + d) v).toReal := by
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ellipticPowerProfile_ne_top B.smooth_a hb' hVc hv (m + 1 + d))) (hpower hv)
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hD] using h
  have hgerm : v =ᶠ[𝓝 x] u :=
    Filter.mem_of_superset (hV.mem_nhds (hKV hx)) hvu
  have hderiv : iteratedFDeriv ℝ m v x = iteratedFDeriv ℝ m u x :=
    (hgerm.iteratedFDeriv ℝ m).self_of_nhds
  rw [← hderiv, ← hsum]
  calc
    ‖iteratedFDeriv ℝ m v x‖ ≤ A * (derivativeProfile 2 W (m + 1 + d) v).toReal :=
      hjet hv x hx
    _ ≤ A * (D * (ellipticPowerProfile B.a b' V (m + 1 + d) v).toReal) :=
      mul_le_mul_of_nonneg_left hprofile hA.le
    _ ≤ A * (D + 1) * (ellipticPowerProfile B.a b' V (m + 1 + d) v).toReal := by
      nlinarith [ENNReal.toReal_nonneg (a := ellipticPowerProfile B.a b' V (m + 1 + d) v)]

end Poincare.Analysis.Elliptic.InteriorEstimates
