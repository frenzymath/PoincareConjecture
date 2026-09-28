import PoincareConjecture.Proofs.M09.SmoothJoinCutoff
import PoincareConjecture.Definitions.Ch01.RiemannianMetric
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option autoImplicit false

open scoped Manifold ContDiff Topology
open Filter

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

noncomputable def smoothChartJoin (α β : ℝ → M) (p : M) (c r d s : ℝ) : M := by
  classical
  let e := chartAt E p
  exact if s < c - r then α s else if c + r < s then β s else
    e.symm (smoothJoinBlend (fun t ↦ e (α t)) (fun t ↦ e (β t)) c d s)

theorem smoothChartJoin_eq_middle (α β : ℝ → M) (p : M) (c r d s : ℝ)
    (hs : s ∈ Set.Icc (c - r) (c + r)) :
    smoothChartJoin (n := n) α β p c r d s = (chartAt E p).symm
      (smoothJoinBlend (fun t ↦ (chartAt E p) (α t)) (fun t ↦ (chartAt E p) (β t)) c d s) := by
  simp only [smoothChartJoin, if_neg (not_lt.mpr hs.1), if_neg (not_lt.mpr hs.2)]

theorem smoothChartJoin_eq_left (α β : ℝ → M) (p : M) (c r d : ℝ)
    (hr : 0 < r) (hd : 0 < d)
    (hα : ∀ s ∈ Set.Icc (c - r) (c + r), α s ∈ (chartAt E p).source)
    (s : ℝ) (hs : s ≤ c - d) : smoothChartJoin (n := n) α β p c r d s = α s := by
  by_cases hsr : s < c - r
  · simp only [smoothChartJoin, if_pos hsr]
  · have hsr' : s ≤ c + r := by linarith
    rw [smoothChartJoin_eq_middle (n := n) α β p c r d s ⟨le_of_not_gt hsr, hsr'⟩,
      smoothJoinBlend_eq_left _ _ c hd hs]
    exact (chartAt E p).left_inv (hα s ⟨le_of_not_gt hsr, hsr'⟩)

theorem smoothChartJoin_eq_right (α β : ℝ → M) (p : M) (c r d : ℝ)
    (hr : 0 < r) (hd : 0 < d)
    (hβ : ∀ s ∈ Set.Icc (c - r) (c + r), β s ∈ (chartAt E p).source)
    (s : ℝ) (hs : c + d ≤ s) : smoothChartJoin (n := n) α β p c r d s = β s := by
  have hsr : ¬s < c - r := by linarith
  by_cases hrs : c + r < s
  · simp only [smoothChartJoin, if_neg hsr, if_pos hrs]
  · rw [smoothChartJoin_eq_middle (n := n) α β p c r d s ⟨le_of_not_gt hsr, le_of_not_gt hrs⟩,
      smoothJoinBlend_eq_right _ _ c hd hs]
    exact (chartAt E p).left_inv (hβ s ⟨le_of_not_gt hsr, le_of_not_gt hrs⟩)

theorem smoothChartJoin_contMDiffOn (α β : ℝ → M) (p : M) (c r d : ℝ)
    (hr : 0 < r) (hd : 0 < d) (hdr : d < r) (D : Set ℝ) (hD : IsOpen D)
    (hI : Set.Icc (c - r) (c + r) ⊆ D)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α D)
    (hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ β D)
    (hαs : ∀ s ∈ Set.Icc (c - r) (c + r), α s ∈ (chartAt E p).source)
    (hβs : ∀ s ∈ Set.Icc (c - r) (c + r), β s ∈ (chartAt E p).source)
    (hblend : ∀ s ∈ Set.Ioo (c - r) (c + r),
      smoothJoinBlend (fun t ↦ (chartAt E p) (α t)) (fun t ↦ (chartAt E p) (β t)) c d s ∈
        (chartAt E p).target) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (smoothChartJoin (n := n) α β p c r d) D := by
  have hac : ContDiffOn ℝ ∞ (fun t ↦ (chartAt E p) (α t)) (Set.Ioo (c - r) (c + r)) :=
    (contMDiffOn_chart.comp (hα.mono (Set.Ioo_subset_Icc_self.trans hI))
      (fun s hs ↦ hαs s (Set.Ioo_subset_Icc_self hs))).contDiffOn
  have hbc : ContDiffOn ℝ ∞ (fun t ↦ (chartAt E p) (β t)) (Set.Ioo (c - r) (c + r)) :=
    (contMDiffOn_chart.comp (hβ.mono (Set.Ioo_subset_Icc_self.trans hI))
      (fun s hs ↦ hβs s (Set.Ioo_subset_Icc_self hs))).contDiffOn
  have hmid := (contMDiffOn_chart_symm (I := 𝓡 n) (x := p)).comp
    (smoothJoinBlend_contDiffOn _ _ c d _ hac hbc).contMDiffOn hblend
  intro s hs
  by_cases hl : s < c - d
  · have heq : smoothChartJoin (n := n) α β p c r d =ᶠ[𝓝 s] α := by
      filter_upwards [gt_mem_nhds hl] with t ht
      exact smoothChartJoin_eq_left (n := n) α β p c r d hr hd hαs t ht.le
    exact ((hα.contMDiffAt (hD.mem_nhds hs)).congr_of_eventuallyEq heq).contMDiffWithinAt
  by_cases hh : c + d < s
  · have heq : smoothChartJoin (n := n) α β p c r d =ᶠ[𝓝 s] β := by
      filter_upwards [lt_mem_nhds hh] with t ht
      exact smoothChartJoin_eq_right (n := n) α β p c r d hr hd hβs t ht.le
    exact ((hβ.contMDiffAt (hD.mem_nhds hs)).congr_of_eventuallyEq heq).contMDiffWithinAt
  have hsI : s ∈ Set.Ioo (c - r) (c + r) := ⟨by linarith, by linarith⟩
  have heq : smoothChartJoin (n := n) α β p c r d =ᶠ[𝓝 s]
      (fun t ↦ (chartAt E p).symm
        (smoothJoinBlend (fun t ↦ (chartAt E p) (α t)) (fun t ↦ (chartAt E p) (β t)) c d t)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hsI] with t ht
    exact smoothChartJoin_eq_middle (n := n) α β p c r d t (Set.Ioo_subset_Icc_self ht)
  exact ((hmid.contMDiffAt (isOpen_Ioo.mem_nhds hsI)).congr_of_eventuallyEq heq).contMDiffWithinAt

end PoincareConjecture.Proofs.M09
