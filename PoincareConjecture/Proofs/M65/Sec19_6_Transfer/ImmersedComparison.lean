import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationFilledApproximation
import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedWeightedComparison
import PoincareConjecture.Statements.M64Comparison











set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology intervalIntegral

namespace PoincareConjecture

variable {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M]
  {a b circumference : ℝ}






theorem m65ImmersedFillingAreaComparison_of_diskComparison
    (F : RicciFlow 3 M (Icc a b)) (P : M62.CircleProductData F circumference)
    (disks : ∀ q ∈ Ioo a b, M64DiskAreaComparison P q)
    (embedded : M65EmbeddedFillingAreaInequality F) :
    M65ImmersedFillingAreaComparison F := by
  intro J hJ hJF C hCSF s t hst hI
  obtain ⟨ell, r, Cn, exceptions, L, hell, htr, hKJ, _, hinj, hres, hlength,
    _, _, hcontinuous, hlimit⟩ :=
    m65Exists_generic_filled_approximations F P hJ hJF
      (fun q hq => disks q (hJF hq)) C hCSF hst hI
  have hOJ : Ioo ell r ⊆ J := Ioo_subset_Icc_self.trans hKJ
  have hIO : Icc s t ⊆ Ioo ell r := fun q hq =>
    ⟨hell.trans_le hq.1, hq.2.trans_lt htr⟩
  let A : ℕ → ℝ → ℝ := fun n q => fillingArea (F.metric q) ((Cn n).loops q)
  let A0 : ℝ → ℝ := fun q => fillingArea (F.metric q) (C.loops q)
  let eta : ℕ → ℝ := fun n => (1 / ((n : ℝ) + 1)) * L
  have hupper (n : ℕ) : ∀ q ∈ Ioo s t, q ∉ exceptions n → ∀ delta : ℝ,
      0 < delta → ∀ᶠ h in 𝓝[>] (0 : ℝ), (A n (q + h) - A n q) / h ≤
        -2 * Real.pi - flowScalarCurvatureInfimum F q * A n q / 2 + eta n + delta := by
    intro q hq hnot delta hdelta
    have hqK : q ∈ Icc s t := Ioo_subset_Icc_self hq
    have hepsilon : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
    have hh := embedded (Ioo ell r) isOpen_Ioo (hOJ.trans hJF) (Cn n) q (hIO hqK)
      (hinj n q hqK hnot) (1 / ((n : ℝ) + 1)) hepsilon (hres n q hqK) delta hdelta
    have herr := mul_le_mul_of_nonneg_left (hlength n q hqK) hepsilon
    filter_upwards [hh] with h hh
    dsimp only [A, eta]
    linarith
  have hcomparison (n : ℕ) :
      m65WeightedArea F (A n) t - eta n * (∫ q in a..t, m65AreaWeight F q) ≤
        m65WeightedArea F (A n) s - eta n * (∫ q in a..s, m65AreaWeight F q) :=
    M65Perturbation.weighted_comparison_finite F isCompact_univ (A n) (eta n)
      (exceptions n) hst (hI.trans hJF) ((hcontinuous n).mono hIO) (hupper n)
  have heta : Tendsto eta atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const L
  have hweightedLimit (q : ℝ) (hq : q ∈ Ioo ell r) :
      Tendsto (fun n => m65WeightedArea F (A n) q -
        eta n * (∫ v in a..q, m65AreaWeight F v)) atTop
          (𝓝 (m65WeightedArea F A0 q)) := by
    have hh := (((hlimit q hq).const_mul (m65AreaWeight F q)).add_const
      (2 * Real.pi * ∫ v in a..q, m65AreaWeight F v)).sub
        (heta.mul_const (∫ v in a..q, m65AreaWeight F v))
    simpa only [m65WeightedArea, A, A0, zero_mul, sub_zero] using hh
  have hweighted : m65WeightedArea F A0 t ≤ m65WeightedArea F A0 s :=
    le_of_tendsto_of_tendsto (hweightedLimit t (hIO ⟨hst, le_rfl⟩))
      (hweightedLimit s (hIO ⟨le_rfl, hst⟩)) (Eventually.of_forall hcomparison)
  have hdiff : m65AreaWeight F t *
      (A0 t - m65RestartedAreaProfile F s (A0 s) t) ≤ 0 := by
    rw [← M65Perturbation.weighted_difference_profile F A0 s t]
    exact sub_nonpos.mpr hweighted
  have hnonpos : A0 t - m65RestartedAreaProfile F s (A0 s) t ≤ 0 := by
    nlinarith [m65AreaWeight_pos F t]
  exact sub_nonpos.mp hnonpos





theorem m65ImmersedFillingAreaComparison_of_embedded
    (F : RicciFlow 3 M (Icc a b)) (V : M64ThreeDimensionalFlowConclusion F)
    (embedded : M65EmbeddedFillingAreaInequality F) :
    M65ImmersedFillingAreaComparison F :=
  m65ImmersedFillingAreaComparison_of_diskComparison F
    (V.flow.geometry.product 1 zero_lt_one)
    (fun q hq => V.disks 1 zero_lt_one q (Ioo_subset_Icc_self hq)) embedded

end PoincareConjecture
