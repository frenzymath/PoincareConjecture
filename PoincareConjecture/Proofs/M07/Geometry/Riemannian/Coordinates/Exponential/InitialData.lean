import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Precompact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem isGeodesicOn_chart_curve (g : RiemannianMetric n M) (p : M)
    {s : Set ℝ} (hs : IsOpen s) {q w : ℝ → EuclideanSpace ℝ (Fin n)}
    (hq : ∀ t ∈ s, q t ∈ (extChartAt (𝓡 n) p).target ∧ HasDerivAt q (w t) t ∧
      HasDerivAt w
        (-coordinateChristoffel (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)
          (q t) (w t) (w t)) t) :
    g.IsGeodesicOn (fun t => (extChartAt (𝓡 n) p).symm (q t)) s := by
  intro t ht
  refine ⟨p, q, w, ?_⟩
  filter_upwards [hs.mem_nhds ht] with u hu
  exact ⟨rfl, hq u hu⟩

theorem exists_geodesic_initial_data (g : RiemannianMetric n M)
    (p : M) (v : EuclideanSpace ℝ (Fin n)) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ γ : ℝ → M,
      g.IsGeodesicOn γ (Ioo (-δ) δ) ∧ γ 0 = p ∧
      HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) v 0 := by
  obtain ⟨q, w, ε, hε, hq0, hw0, hqw⟩ := g.exists_chart_geodesic p v
  let δ := min ε (1 / 2)
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hsub : Ioo (-δ) δ ⊆ Ioo (-ε) ε := by
    intro t ht
    exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) ht.1,
      lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
  let γ := fun t => (extChartAt (𝓡 n) p).symm (q t)
  have hq : (fun t => extChartAt (𝓡 n) p (γ t)) =ᶠ[𝓝 0] q := by
    filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-ε) ε by
      constructor <;> linarith)] with t ht
    exact (extChartAt (𝓡 n) p).right_inv (hqw t ht).1
  refine ⟨δ, hδ, (min_le_right ε (1 / 2)).trans_lt (by norm_num), γ,
    g.isGeodesicOn_chart_curve p isOpen_Ioo (fun t ht =>
      ⟨(hqw t (hsub ht)).1, (hqw t (hsub ht)).2.1, (hqw t (hsub ht)).2.2.1⟩), ?_, ?_⟩
  · dsimp [γ]
    rw [hq0]
    exact (extChartAt (𝓡 n) p).left_inv (mem_extChartAt_source p)
  · have hd := (hqw 0 (show (0 : ℝ) ∈ Ioo (-ε) ε by
      constructor <;> linarith)).2.1
    rw [hw0] at hd
    exact hd.congr_of_eventuallyEq hq

theorem IsGeodesicOn.tangentNorm_initial
    {γ : ℝ → M} {s : Set ℝ} (hγ : g.IsGeodesicOn γ s) (h0 : (0 : ℝ) ∈ s)
    {p : M} (hp : γ 0 = p) {v : EuclideanSpace ℝ (Fin n)}
    (hv : HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) v 0) :
    g.tangentNorm (γ 0) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ 0 1) =
      Real.sqrt (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
        (extChartAt (𝓡 n) p p) v v) := by
  obtain ⟨r, q, w, hlocal⟩ := hγ 0 h0
  have hcont : ContinuousAt γ 0 := by
    have h := hlocal.self_of_nhds
    exact (((contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) r).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) r).mem_nhds h.2.1)).continuousAt.comp
        h.2.2.1.continuousAt).congr (hlocal.mono fun _ hu => hu.1.symm)
  have heq : γ =ᶠ[𝓝 0] fun t =>
      (extChartAt (𝓡 n) p).symm (extChartAt (𝓡 n) p (γ t)) := by
    filter_upwards [hcont.preimage_mem_nhds (by
      rw [hp]
      exact (isOpen_extChartAt_source (I := 𝓡 n) p).mem_nhds
        (mem_extChartAt_source p))] with t ht
    exact ((extChartAt (𝓡 n) p).left_inv ht).symm
  rw [heq.mfderiv_eq, heq.self_of_nhds]
  have h := g.tangentNorm_chart_curve p hv (by
    rw [hp]
    exact mem_extChartAt_target p)
  simpa only [hp] using h

theorem IsGeodesicOn.edist_le_initial_speed
    {γ : ℝ → M} {a b : ℝ} (hγ : g.IsGeodesicOn γ (Ioo a b))
    (h0 : (0 : ℝ) ∈ Ioo a b) {p : M} (hp : γ 0 = p)
    {v : EuclideanSpace ℝ (Fin n)}
    (hv : HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) v 0)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    g.edist p (γ t) ≤
      ENNReal.ofReal (Real.sqrt (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
        (extChartAt (𝓡 n) p p) v v)) * ENNReal.ofReal |t| := by
  obtain ⟨C, hC⟩ := hγ.exists_constant_tangentNorm (h0.1.trans h0.2)
  have hC0 := hC 0 h0
  rw [hγ.tangentNorm_initial h0 hp hv] at hC0
  have h := hγ.edist_le_of_tangentNorm_eq hC h0 ht
  rw [hp] at h
  simpa only [hC0, ENNReal.ofReal_coe_nnreal, edist_dist, Real.dist_eq,
    zero_sub, abs_neg] using h

end PoincareConjecture.RiemannianMetric
