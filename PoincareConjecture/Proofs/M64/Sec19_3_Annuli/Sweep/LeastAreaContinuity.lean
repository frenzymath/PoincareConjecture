import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Sweep.LeastAreaComparison
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Sweep.NonemptyEvolution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)}

theorem m64LeastAnnulusArea_continuous_of_initial
    (hcompact : IsCompact (univ : Set M))
    {c0 c1 : ℝ → ℝ → M}
    (hc0 : M63C2ShrinkingCurveOn F c0 (Icc a b))
    (hc1 : M63C2ShrinkingCurveOn F c1 (Icc a b))
    (A : M64Annulus (F.metric a) (fun x => c0 x a) (fun x => c1 x a)) :
    ContinuousOn (fun t => m64LeastAnnulusArea (F.metric t)
      (fun x => c0 x t) (fun x => c1 x t)) (Icc a b) := by
  let f := fun t => m64LeastAnnulusArea (F.metric t) (fun x => c0 x t) (fun x => c1 x t)
  intro s hs
  obtain ⟨As⟩ := m64Annulus_nonempty_of_c2_sweeps hcompact hc0 hc1
    ⟨le_rfl, hs.1.trans hs.2⟩ hs A
  obtain ⟨K, C, _hK, _hC, hcomp⟩ := m64LeastAnnulusArea_two_sided_local hcompact hc0 hc1 hs As
  let k : ℝ → ℝ := fun t => Real.exp ((n : ℝ) * K * |t - s|) ^ 2
  have hk (t : ℝ) : 0 < k t := sq_pos_of_pos (Real.exp_pos _)
  have hkcont : Continuous k := by unfold k; fun_prop
  let lower : ℝ → ℝ := fun t => (f s - C * |t - s|) / k t
  let upper : ℝ → ℝ := fun t => k t * (f s + C * |t - s|)
  have habs : Continuous (fun t : ℝ => |t - s|) := (continuous_id.sub continuous_const).abs
  have hlcont : Continuous lower :=
    (continuous_const.sub (continuous_const.mul habs)).div hkcont (fun t => (hk t).ne')
  have hucont : Continuous upper :=
    hkcont.mul (continuous_const.add (continuous_const.mul habs))
  have hlval : lower s = f s := by simp [lower, k]
  have huval : upper s = f s := by simp [upper, k]
  have hlow : Tendsto lower (𝓝[Icc a b] s) (𝓝 (f s)) := by
    rw [← hlval]
    exact hlcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hupp : Tendsto upper (𝓝[Icc a b] s) (𝓝 (f s)) := by
    rw [← huval]
    exact hucont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  change Tendsto f (𝓝[Icc a b] s) (𝓝 (f s))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change (f s - C * |t - s|) / k t ≤ f t
    apply (div_le_iff₀ (hk t)).mpr
    have h := (hcomp t ht).2
    change f s ≤ k t * f t + C * |t - s| at h
    nlinarith
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hcomp t ht).1

theorem m64AnnulusFlow_continuous_of_initial
    (hcompact : IsCompact (univ : Set M))
    {circumference : ℝ} (hcirc : 0 < circumference)
    (P : M62.CircleProductData F circumference)
    {c0 c1 : ℝ → ℝ → P.charts.Point}
    (hc0 : M63C2ShrinkingCurveOn P.flow c0 (Icc a b))
    (hc1 : M63C2ShrinkingCurveOn P.flow c1 (Icc a b))
    (A : M64Annulus (P.flow.metric a) (fun x => c0 x a) (fun x => c1 x a)) :
    ContinuousOn (m64FlowAnnulusArea P c0 c1) (Icc a b) := by
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  let : Fact (0 < circumference) := ⟨hcirc⟩
  have hcompactP : IsCompact (univ : Set P.charts.Point) := isCompact_univ
  exact m64LeastAnnulusArea_continuous_of_initial hcompactP hc0 hc1 A

end PoincareConjecture
