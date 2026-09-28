import PoincareConjecture.Proofs.M58.Mathlib.LocalContractionWeighted
import Mathlib.Geometry.Manifold.BumpFunction

set_option autoImplicit false

open Set Filter Function
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M58

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M]

noncomputable def chartContractionSequence
    (L : List (Σ c : M, SmoothBumpFunction I c)) (v : ℝ × (M × M)) : M :=
  match L with
  | [] => v.2.2
  | a :: L => weightedChartContraction I a.1 a.2
      (v.1, v.2.1, chartContractionSequence L v)

theorem chartContractionSequence_zero
    (L : List (Σ c : M, SmoothBumpFunction I c)) (p q : M) :
    chartContractionSequence I L (0, p, q) = q := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simpa only [chartContractionSequence, weightedChartContraction_zero] using ih

theorem chartContractionSequence_diagonal
    (L : List (Σ c : M, SmoothBumpFunction I c)) (t : ℝ) (p : M) :
    chartContractionSequence I L (t, p, p) = p := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [chartContractionSequence, ih, weightedChartContraction_diagonal]

theorem exists_finite_bump_plateau_cover (hcompact : IsCompact (univ : Set M)) :
    ∃ L : List (Σ c : M, SmoothBumpFunction I c),
      ∀ p : M, ∃ a ∈ L, (a.2 : M → ℝ) =ᶠ[𝓝 p] 1 := by
  classical
  let b : ∀ c : M, SmoothBumpFunction I c := fun _ => Classical.choice inferInstance
  let U : M → Set M := fun c => interior {p | b c p = 1}
  have hcover : (univ : Set M) ⊆ ⋃ c, U c := by
    intro p _
    apply mem_iUnion.mpr
    refine ⟨p, ?_⟩
    exact mem_interior_iff_mem_nhds.mpr (b p).eventuallyEq_one
  obtain ⟨s, hs⟩ := hcompact.elim_finite_subcover U (fun _ => isOpen_interior) hcover
  refine ⟨s.toList.map (fun c => ⟨c, b c⟩), ?_⟩
  intro p
  obtain ⟨c, hc, hpc⟩ := mem_iUnion₂.mp (hs (mem_univ p))
  refine ⟨⟨c, b c⟩, List.mem_map.mpr ⟨c, Finset.mem_toList.mpr hc, rfl⟩, ?_⟩
  exact mem_interior_iff_mem_nhds.mp hpc

variable [T2Space M] [I.Boundaryless] [IsManifold I ∞ M]

theorem contMDiffAt_chartContractionSequence_diagonal
    (L : List (Σ c : M, SmoothBumpFunction I c)) (t : ℝ) (p : M) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (I.prod I)) I ∞
      (chartContractionSequence I L) (t, p, p) := by
  induction L with
  | nil => exact contMDiffAt_snd.comp _ contMDiffAt_snd
  | cons a L ih =>
    have hinput : ContMDiffAt (𝓘(ℝ, ℝ).prod (I.prod I))
        (𝓘(ℝ, ℝ).prod (I.prod I)) ∞
        (fun v : ℝ × (M × M) => (v.1, v.2.1, chartContractionSequence I L v))
        (t, p, p) :=
      contMDiffAt_fst.prodMk ((contMDiffAt_fst.comp _ contMDiffAt_snd).prodMk ih)
    exact (contMDiffAt_weightedChartContraction_diagonal I a.1 a.2 a.2.contMDiff
      a.2.tsupport_subset_extChartAt_source t p).comp_of_eq hinput (by
        simp only [chartContractionSequence_diagonal])

theorem chartContractionSequence_one_eventually
    (L : List (Σ c : M, SmoothBumpFunction I c)) (p : M)
    (hplateau : ∃ a ∈ L, (a.2 : M → ℝ) =ᶠ[𝓝 p] 1) :
    ∀ᶠ v : M × M in 𝓝 (p, p), chartContractionSequence I L (1, v) = v.1 := by
  induction L with
  | nil => simp only [List.not_mem_nil, false_and, exists_false] at hplateau
  | cons a L ih =>
    obtain ⟨b, hb, hbp⟩ := hplateau
    rcases List.mem_cons.mp hb with hba | hb
    · subst b
      have hb1 : a.2 p = 1 := hbp.eq_of_nhds
      have hp : p ∈ (extChartAt I a.1).source :=
        a.2.tsupport_subset_extChartAt_source (subset_closure (by
          change a.2 p ≠ 0
          rw [hb1]
          exact one_ne_zero))
      have htail : ContinuousAt
          (fun v : M × M => chartContractionSequence I L (1, v)) (p, p) :=
        (contMDiffAt_chartContractionSequence_diagonal I L 1 p).continuousAt.comp
          (continuousAt_const.prodMk continuousAt_id)
      have htail' : Tendsto (fun v : M × M => chartContractionSequence I L (1, v))
          (𝓝 (p, p)) (𝓝 p) := by
        simpa only [ContinuousAt, chartContractionSequence_diagonal] using htail
      have hfirst : ∀ᶠ v : M × M in 𝓝 (p, p), v.1 ∈ (extChartAt I a.1).source :=
        (continuous_fst.tendsto (p, p)) ((isOpen_extChartAt_source a.1).mem_nhds hp)
      have hlast : ∀ᶠ v : M × M in 𝓝 (p, p),
          chartContractionSequence I L (1, v) ∈ (extChartAt I a.1).source :=
        htail' ((isOpen_extChartAt_source a.1).mem_nhds hp)
      filter_upwards [hfirst, hlast, hbp.comp_tendsto (continuous_fst.tendsto (p, p))]
        with v hvp hvq hvb
      exact weightedChartContraction_one I a.1 a.2 _ _ hvp hvq hvb
    · filter_upwards [ih ⟨b, hb, hbp⟩] with v hv
      simp only [chartContractionSequence, hv, weightedChartContraction_diagonal]

end PoincareConjecture.Proofs.M58
