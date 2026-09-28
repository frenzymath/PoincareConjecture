import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalConeWeakFilling
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalConeH1Radius

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "circleMu" => volume.restrict (Icc (0 : ℝ) curvePeriod)

theorem m64ChartReadable_uniform_H1_cone_radius
    (g : RiemannianMetric n M) (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsEmbedding e) (hread : M60.SUChartReadable (n := n) e) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gamma : ℝ → M), Continuous gamma → Function.Periodic gamma curvePeriod →
        (∀ x ∈ Icc (0 : ℝ) curvePeriod, dist (e (gamma x)) (e (gamma 0)) < delta) →
        ∀ (w : ℕ → ℝ → E),
          (∀ j, ContDiff ℝ 1 (w j)) → (∀ j, Function.Periodic (w j) curvePeriod) →
          TendstoUniformlyOn w (e ∘ gamma) atTop (Icc (0 : ℝ) curvePeriod) →
          ∀ v : ℝ → E, MemLp v 2 circleMu →
            Tendsto (fun j => ∫ x in Icc (0 : ℝ) curvePeriod,
              ‖deriv (w j) x - v x‖ ^ 2) atTop (𝓝 0) →
            ∃ A : M64ObservedConeDisk (n := n) e gamma,
              ∀ i, ‖A.column i‖ ^ 2 ≤ C * ∫ x in Icc (0 : ℝ) curvePeriod, ‖v x‖ ^ 2 := by
  classical
  choose U C hU hp hC hfill using m64ChartReadable_local_H1_cone g e he hread
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover U hU
    (fun q _ => mem_iUnion.mpr ⟨q, hp q⟩)
  choose V hV hpre using fun p => hei.isInducing.isOpen_iff.mp (hU p)
  have hcover : range e ⊆ ⋃ p : (↑T : Set M), V p.1 := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨p, hpT, hq⟩ := mem_iUnion₂.mp (hT (mem_univ q))
    refine mem_iUnion.mpr ⟨⟨p, hpT⟩, ?_⟩
    change q ∈ e ⁻¹' V p
    rw [hpre p]
    exact hq
  obtain ⟨delta, hdelta, hball⟩ := lebesgue_number_lemma_of_metric
    (isCompact_range he.continuous) (fun p : (↑T : Set M) => hV p.1) hcover
  refine ⟨delta, hdelta, ∑ p ∈ T, C p, Finset.sum_nonneg (fun p _ => hC p), ?_⟩
  intro gamma hgamma hgammaP hsmall w hw hwP hlim v hv hder
  obtain ⟨p, hpball⟩ := hball (e (gamma 0)) (mem_range_self _)
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hgammaU (x : ℝ) : gamma x ∈ U p.1 := by
    let y := toIcoMod hP 0 x
    have hy : y ∈ Icc (0 : ℝ) curvePeriod :=
      Ico_subset_Icc_self (toIcoMod_mem_Ico' hP x)
    have hxy : gamma y = gamma x := by
      simpa only [y, toIcoMod, neg_smul, sub_eq_add_neg] using
        (hgammaP.zsmul (-toIcoDiv hP 0 x)) x
    rw [← hxy, ← hpre p.1]
    exact hpball (hsmall y hy)
  obtain ⟨A, hA⟩ := hfill p.1 gamma hgamma hgammaP hgammaU w hw hwP hlim v hv hder
  refine ⟨A, fun i => (hA i).trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun q _ => hC q) p.2)
    (integral_nonneg fun x => sq_nonneg ‖v x‖)

theorem m64ChartReadable_small_energy_H1_cone
    (g : RiemannianMetric n M) (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsEmbedding e) (hread : M60.SUChartReadable (n := n) e) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gamma : ℝ → M), Continuous gamma → Function.Periodic gamma curvePeriod →
        ∀ (w : ℕ → ℝ → E),
          (∀ j, ContDiff ℝ 1 (w j)) → (∀ j, Function.Periodic (w j) curvePeriod) →
          TendstoUniformlyOn w (e ∘ gamma) atTop (Icc (0 : ℝ) curvePeriod) →
          ∀ v : ℝ → E, MemLp v 2 circleMu →
            (∀ x ∈ Icc (0 : ℝ) curvePeriod,
              e (gamma x) - e (gamma 0) = ∫ t in (0 : ℝ)..x, v t) →
            Tendsto (fun j => ∫ x in Icc (0 : ℝ) curvePeriod,
              ‖deriv (w j) x - v x‖ ^ 2) atTop (𝓝 0) →
            (∫ x in Icc (0 : ℝ) curvePeriod, ‖v x‖ ^ 2) < epsilon →
            ∃ A : M64ObservedConeDisk (n := n) e gamma,
              ∀ i, ‖A.column i‖ ^ 2 ≤ C * ∫ x in Icc (0 : ℝ) curvePeriod, ‖v x‖ ^ 2 := by
  obtain ⟨delta, hdelta, C, hC, hfill⟩ :=
    m64ChartReadable_uniform_H1_cone_radius g e he hei hread
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  refine ⟨delta ^ 2 / curvePeriod, by positivity, C, hC, ?_⟩
  intro gamma hc hperiod w hw hwP hlim v hv hFTC hder hsmall
  apply hfill gamma hc hperiod ?_ w hw hwP hlim v hv hder
  intro x hx
  have hradius := m64H1Trace_radius_sq_le (e ∘ gamma) v hv hFTC hx
  have hE := (lt_div_iff₀ hP).mp hsmall
  rw [dist_eq_norm]
  change ‖e (gamma x) - e (gamma 0)‖ ^ 2 ≤
    curvePeriod * ∫ t in Icc (0 : ℝ) curvePeriod, ‖v t‖ ^ 2 at hradius
  nlinarith [norm_nonneg (e (gamma x) - e (gamma 0))]

theorem m64ChartReadable_uniform_H1_cone_energy
    (g : RiemannianMetric n M) (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsEmbedding e) (hread : M60.SUChartReadable (n := n) e)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gamma : ℝ → M), Continuous gamma → Function.Periodic gamma curvePeriod →
        ∀ (w : ℕ → ℝ → E),
          (∀ j, ContDiff ℝ 1 (w j)) → (∀ j, Function.Periodic (w j) curvePeriod) →
          TendstoUniformlyOn w (e ∘ gamma) atTop (Icc (0 : ℝ) curvePeriod) →
          ∀ v : ℝ → E, MemLp v 2 circleMu →
            (∀ x ∈ Icc (0 : ℝ) curvePeriod,
              e (gamma x) - e (gamma 0) = ∫ t in (0 : ℝ)..x, v t) →
            Tendsto (fun j => ∫ x in Icc (0 : ℝ) curvePeriod,
              ‖deriv (w j) x - v x‖ ^ 2) atTop (𝓝 0) →
            (∫ x in Icc (0 : ℝ) curvePeriod, ‖v x‖ ^ 2) < epsilon →
            ∃ A : M64ObservedConeDisk (n := n) e gamma,
              A.energy B ≤ C * ∫ x in Icc (0 : ℝ) curvePeriod, ‖v x‖ ^ 2 := by
  obtain ⟨epsilon, hepsilon, C, hC, hfill⟩ :=
    m64ChartReadable_small_energy_H1_cone g e he hei hread
  have hbounded : Bornology.IsBounded (range B) := (isCompact_range hB).isBounded
  obtain ⟨K, hK⟩ := hbounded.exists_norm_le
  refine ⟨epsilon, hepsilon, max K 0 * C, mul_nonneg (le_max_right _ _) hC, ?_⟩
  intro gamma hc hperiod w hw hwP hlim v hv hFTC hder hsmall
  obtain ⟨A, hA⟩ := hfill gamma hc hperiod w hw hwP hlim v hv hFTC hder hsmall
  refine ⟨A, ?_⟩
  exact (A.energy_le_column_bound B hB (le_max_right K 0)
    (fun q => (hK _ (mem_range_self q)).trans (le_max_left _ _)) hA).trans_eq (by ring)

end PoincareConjecture
