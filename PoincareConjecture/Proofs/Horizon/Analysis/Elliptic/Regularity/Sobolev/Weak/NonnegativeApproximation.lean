import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.DifferenceQuotient.MollificationL2

noncomputable section

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal NNReal Convolution

namespace Poincare.Analysis.Sobolev.DifferenceQuotient

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem mollifyEps_nonneg {ε : ℝ} (hε : 0 < ε) {u : E → ℝ}
    (hu : ∀ x, 0 ≤ u x) (x : E) : 0 ≤ mollifyEps hε u x := by
  rw [mollifyEps_apply]
  exact integral_nonneg fun y => mul_nonneg (mollifierEps_nonneg hε y) (hu (x - y))

private theorem mollifyEps_eq_right {ε : ℝ} (hε : 0 < ε) (u : E → ℝ) :
    mollifyEps hε u = u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] mollifierEps hε := by
  funext x
  rw [mollifyEps, convolution_lsmul, convolution_lsmul_swap]
  exact integral_congr_ae <| Filter.Eventually.of_forall fun y => by
    simp only [smul_eq_mul, mul_comm]

theorem tendsto_eLpNorm_mollifyEps_sub {ι : Type*} {l : Filter ι}
    {ε : ι → ℝ} (hε : ∀ i, 0 < ε i) (hεlim : Tendsto ε l (𝓝 0))
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpfin : p ≠ ∞) {u : E → ℝ}
    (hu : MemLp u p volume) :
    Tendsto (fun i => eLpNorm (fun x => mollifyEps (hε i) u x - u x) p volume)
      l (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  obtain ⟨δ, hδ, hbound⟩ :=
    Euclidean.exists_eLpNorm_convolution_mollifierEps_sub_le hp hpfin hu hη
  filter_upwards [hεlim.eventually (gt_mem_nhds hδ)] with i hi
  simpa only [mollifyEps_eq_right] using hbound (ε i) (hε i) hi.le

theorem tendsto_eLpNorm_mollifyEps_partial_sub {ι : Type*} {l : Filter ι}
    {ε : ι → ℝ} (hε : ∀ i, 0 < ε i) (hεlim : Tendsto ε l (𝓝 0))
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpfin : p ≠ ∞) {u g : E → ℝ} {j : Fin d}
    (hu : LocallyIntegrable u volume) (hg : MemLp g p volume)
    (hweak : Weak.HasWeakPartialDeriv j g u univ) :
    Tendsto (fun i => eLpNorm
      (fun x => fderiv ℝ (mollifyEps (hε i) u) x (EuclideanSpace.single j 1) - g x)
      p volume) l (𝓝 0) := by
  simpa only [mollifyEps_partial_eq_mollifyEps_weakPartial _ hu hweak] using
    tendsto_eLpNorm_mollifyEps_sub hε hεlim hp hpfin hg

end Poincare.Analysis.Sobolev.DifferenceQuotient

namespace Poincare.Analysis.Sobolev.Weak

open DifferenceQuotient

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_nonneg_smooth_compactSupport_approx
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpfin : p ≠ ∞)
    {u : E → ℝ} {g : Fin d → E → ℝ} {Ω : Set E}
    (hu : MemLp u p volume) (hg : ∀ j, MemLp (g j) p volume)
    (hweak : ∀ j, HasWeakPartialDeriv j (g j) u univ)
    (hu0 : ∀ x, 0 ≤ u x) (huc : HasCompactSupport u)
    (hΩ : IsOpen Ω) (hsupp : tsupport u ⊆ Ω) :
    ∃ (K : Set E) (φ : ℕ → E → ℝ),
      IsCompact K ∧ K ⊆ Ω ∧ tsupport u ⊆ K ∧
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (φ k)) ∧
      (∀ k, tsupport (φ k) ⊆ K) ∧ (∀ k x, 0 ≤ φ k x) ∧
      Tendsto (fun k => eLpNorm (fun x => φ k x - u x) p volume) atTop (𝓝 0) ∧
      ∀ j, Tendsto (fun k => eLpNorm
        (fun x => fderiv ℝ (φ k) x (EuclideanSpace.single j 1) - g j x)
        p volume) atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hδΩ⟩ := huc.isCompact.exists_cthickening_subset_open hΩ hsupp
  let ε : ℕ → ℝ := fun k => min δ (1 / (k + 1 : ℝ))
  have hε : ∀ k, 0 < ε k := fun k => lt_min hδ (by positivity)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := δ)).min
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [min_eq_right hδ.le] using h
  let K := cthickening δ (tsupport u)
  let φ : ℕ → E → ℝ := fun k => mollifyEps (hε k) u
  refine ⟨K, φ, huc.isCompact.cthickening, hδΩ,
    self_subset_cthickening (tsupport u), ?_, ?_, ?_, ?_, ?_⟩
  · exact fun k => mollifyEps_contDiff (hε k) (hu.locallyIntegrable hp)
  · intro k
    rw [show φ k = u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      mollifierEps (hε k) from mollifyEps_eq_right (hε k) u]
    exact (Euclidean.tsupport_convolution_mollifierEps_subset_thickening (hε k)).trans
      (cthickening_mono (min_le_left _ _) _)
  · exact fun k x => mollifyEps_nonneg (hε k) hu0 x
  · exact tendsto_eLpNorm_mollifyEps_sub hε hεlim hp hpfin hu
  · exact fun j => tendsto_eLpNorm_mollifyEps_partial_sub hε hεlim hp hpfin
      (hu.locallyIntegrable hp) (hg j) (hweak j)

end Poincare.Analysis.Sobolev.Weak
