import PoincareConjecture.Proofs.M59.Mathlib.LocalChartApproximation

set_option autoImplicit false

open Set Filter Function
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M59

variable {E H X F K M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [T2Space X] [NormalSpace X] [SigmaCompactSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
  (J : ModelWithCorners ℝ F K) [J.Boundaryless]
  [MetricSpace M] [ChartedSpace K M] [IsManifold J ∞ M]

omit [IsManifold I ∞ X] [NormalSpace X] [SigmaCompactSpace X]
  [J.Boundaryless] [IsManifold J ∞ M] in

theorem exists_finite_chart_tolerance
    (L : List ((Σ x : X, SmoothBumpFunction I x) × M)) (f : X → M) (hf : Continuous f)
    (hL : ∀ a ∈ L, ∀ x ∈ tsupport a.1.2, f x ∈ (extChartAt J a.2).source) :
    ∃ delta > 0, ∀ g : X → M, (∀ x, dist (g x) (f x) < delta) →
      ∀ a ∈ L, ∀ x ∈ tsupport a.1.2, g x ∈ (extChartAt J a.2).source := by
  induction L with
  | nil => exact ⟨1, zero_lt_one, fun _ _ _ h => False.elim (List.not_mem_nil h)⟩
  | cons a L ih =>
    obtain ⟨d, hd, hrest⟩ := ih (fun c hc => hL c (List.mem_cons_of_mem _ hc))
    have hcompact := a.1.2.hasCompactSupport.image hf
    have hsubset : f '' tsupport a.1.2 ⊆ (extChartAt J a.2).source := by
      rintro _ ⟨x, hx, rfl⟩
      exact hL a (List.mem_cons_self) x hx
    obtain ⟨e, he, hnear⟩ := hcompact.exists_thickening_subset_open
      (isOpen_extChartAt_source a.2) hsubset
    refine ⟨min d e, lt_min hd he, ?_⟩
    intro g hg c hc x hx
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hnear (Metric.mem_thickening_iff.mpr
        ⟨f x, ⟨x, hx, rfl⟩, (hg x).trans_le (min_le_right _ _)⟩)
    · exact hrest g (fun x => (hg x).trans_le (min_le_left _ _)) c hc x hx

theorem exists_finite_chart_approximation
    (L : List ((Σ x : X, SmoothBumpFunction I x) × M))
    (f : X → M) (hf : Continuous f)
    (hL : ∀ a ∈ L, ∀ x ∈ tsupport a.1.2, f x ∈ (extChartAt J a.2).source)
    (p : M) {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ g : X → M, Continuous g ∧ (∀ x, dist (g x) (f x) < epsilon) ∧
      (∀ x, f x = p → g x = p) ∧
      (∀ x, ContMDiffAt I J ∞ f x → ContMDiffAt I J ∞ g x) ∧
      ∀ a ∈ L, ∀ x, (a.1.2 : X → ℝ) =ᶠ[𝓝 x] 1 → ContMDiffAt I J ∞ g x := by
  induction L generalizing f epsilon with
  | nil =>
    exact ⟨f, hf, fun x => by simpa only [dist_self] using he,
      fun _ h => h, fun _ h => h, fun _ h => False.elim (List.not_mem_nil h)⟩
  | cons a L ih =>
    obtain ⟨delta, hd, htolerance⟩ := exists_finite_chart_tolerance I J L f hf
      (fun c hc => hL c (List.mem_cons_of_mem _ hc))
    obtain ⟨g, hg, hgf, hgp, hgs, hga⟩ := exists_local_chart_approximation I J a.2 a.1.2
      a.1.2.contMDiff a.1.2.hasCompactSupport (fun _ => a.1.2.mem_Icc) f hf
      (hL a List.mem_cons_self) p (lt_min (half_pos he) hd)
    have hgL : ∀ c ∈ L, ∀ x ∈ tsupport c.1.2, g x ∈ (extChartAt J c.2).source :=
      htolerance g (fun x => (hgf x).trans_le (min_le_right _ _))
    obtain ⟨k, hk, hkg, hkp, hks, hkL⟩ := ih g hg hgL (half_pos he)
    refine ⟨k, hk, ?_, fun x hx => hkp x (hgp x hx),
      fun x hx => hks x (hgs x hx), ?_⟩
    · intro x
      have hsum := add_lt_add (hkg x) ((hgf x).trans_le (min_le_left _ _))
      have hdist := (dist_triangle (k x) (g x) (f x)).trans_lt hsum
      simpa only [add_halves] using hdist
    · intro c hc x hx
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hks x (hga x hx)
      · exact hkL c hc x hx

theorem exists_compact_manifold_approximation
    (f : X → M) (hf : Continuous f) {S : Set X} (hS : IsCompact S)
    (p : M) {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ g : X → M, Continuous g ∧ (∀ x, dist (g x) (f x) < epsilon) ∧
      (∀ x, f x = p → g x = p) ∧ ∀ x ∈ S, ContMDiffAt I J ∞ g x := by
  classical
  have hb : ∀ x : X, ∃ b : SmoothBumpFunction I x,
      ∀ y ∈ tsupport b, f y ∈ (extChartAt J (f x)).source := by
    intro x
    have hsource : f ⁻¹' (extChartAt J (f x)).source ∈ 𝓝 x :=
      hf.continuousAt ((isOpen_extChartAt_source (f x)).mem_nhds (mem_extChartAt_source (f x)))
    obtain ⟨b, _, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp hsource
    exact ⟨b, hb⟩
  choose b hb using hb
  let U : X → Set X := fun x => interior {y | b x y = 1}
  have hcover : S ⊆ ⋃ x, U x := by
    intro x _
    exact mem_iUnion.mpr ⟨x, mem_interior_iff_mem_nhds.mpr (b x).eventuallyEq_one⟩
  obtain ⟨s, hs⟩ := hS.elim_finite_subcover U (fun _ => isOpen_interior) hcover
  let L : List ((Σ x : X, SmoothBumpFunction I x) × M) :=
    s.toList.map (fun x => (⟨x, b x⟩, f x))
  have hL : ∀ a ∈ L, ∀ x ∈ tsupport a.1.2, f x ∈ (extChartAt J a.2).source := by
    intro a ha
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
    exact hb x
  obtain ⟨g, hg, herr, hfix, _, hsmooth⟩ := exists_finite_chart_approximation I J L f hf hL p he
  refine ⟨g, hg, herr, hfix, ?_⟩
  intro x hx
  obtain ⟨c, hc, hcx⟩ := mem_iUnion₂.mp (hs hx)
  exact hsmooth (⟨c, b c⟩, f c)
    (List.mem_map.mpr ⟨c, Finset.mem_toList.mpr hc, rfl⟩) x
    (mem_interior_iff_mem_nhds.mp hcx)

end PoincareConjecture.Proofs.M59
