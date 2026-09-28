import PoincareConjecture.Proofs.M32.Claim11_32.Extension.AnalyticGradient


















set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M32

variable {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]

private theorem old_interval_mem_nhds
    (H : SingularTimeAssumptions F T M) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    F.interval ∈ 𝓝 t :=
  mem_of_superset (Ioo_mem_nhds ht.1 ht.2)
    (fun _ hs => H.interval_exhausts_preterminal ⟨hs.1.le, hs.2⟩)

private theorem box_interval_mem_nhds
    (G : GeneralizedRicciFlowData.{u}) (b : G.box_index) {t : ℝ}
    (ht : t ∈ (G.box b).interval) (hI : G.interval ∈ 𝓝 t) :
    (G.box b).interval ∈ 𝓝 t := by
  obtain ⟨U, hU, heq⟩ := (G.box b).relatively_open
  rw [heq] at ht ⊢
  exact inter_mem hI (hU.mem_nhds ht.2)

private theorem box_time_mem (G : GeneralizedRicciFlowData.{u})
    (b : G.box_index) {t : ℝ} (ht : t ∈ (G.box b).interval) : t ∈ G.interval := by
  obtain ⟨U, _, heq⟩ := (G.box b).relatively_open
  exact (heq ▸ ht).1



theorem extension_box_scalar_evolution_bound
    (hM04 : RicciFlowCurvatureTheory.{u})
    (H : SingularTimeAssumptions F T M) (E : GeneralizedFlowExtension F T)
    (b : E.extended.box_index) {t : ℝ} (ht : t ∈ Ioo 0 T)
    (hb : t ∈ (E.extended.box b).interval)
    (x : (E.extended.box b).carrier.carrier)
    (hx : H.r₀⁻¹ ^ 2 ≤ ((E.extended.box b).flow.connection t).scalarCurvature x) :
    |((E.extended.box b).flow.connection t).laplacian
        ((E.extended.box b).flow.connection t).scalarCurvature x +
      2 * ((E.extended.box b).flow.connection t).ricciNormSq x| ≤
      H.analytic_constant * ((E.extended.box b).flow.connection t).scalarCurvature x ^ 2 := by
  have htF : t ∈ F.interval := H.interval_exhausts_preterminal ⟨ht.1.le, ht.2⟩
  obtain ⟨a, ha, y, hay⟩ := F.box_covers t
    (E.inverse t htF ((E.extended.box b).forward t hb x))
  obtain ⟨c, z, δ, hδ, hcompat⟩ := E.vertical_compatibility a t ha y
  obtain ⟨hc, hc_eq⟩ := hcompat t ha (by simpa using hδ)
  rw [E.spacetime_slices t htF, hay, E.right_inverse] at hc_eq
  have hbc : (E.extended.box b).forward t hb x =
      (E.extended.box c).forward t hc z := eq_of_heq (Sigma.mk.inj hc_eq).2
  have hFn := old_interval_mem_nhds H ht
  have haN := box_interval_mem_nhds F a ha hFn
  have hbN := box_interval_mem_nhds E.extended b hb
    (mem_of_superset hFn E.old_times)
  have heq : (fun s => ((E.extended.box b).flow.connection s).scalarCurvature x) =ᶠ[𝓝 t]
      (fun s => ((F.box a).flow.connection s).scalarCurvature y) := by
    filter_upwards [haN, hbN, Metric.ball_mem_nhds t hδ] with s hsa hsb hsδ
    obtain ⟨hsc, hext⟩ := hcompat s hsa
      (by simpa only [Metric.mem_ball, Real.dist_eq] using hsδ)
    have hsF := box_time_mem F a hsa
    rw [E.spacetime_slices s hsF] at hext
    have hext' := eq_of_heq (Sigma.mk.inj hext).2
    calc
      _ = (E.extended.connection s).scalarCurvature ((E.extended.box b).forward s hsb x) :=
        (box_scalar_pullback E.extended b s hsb x).symm
      _ = (E.extended.connection s).scalarCurvature ((E.extended.box c).forward s hsc z) :=
        congrArg _ (E.extended.vertical_compatibility b c t hb hc x z hbc s hsb hsc)
      _ = (F.connection s).scalarCurvature ((F.box a).forward s hsa y) := by
        rw [← hext', E.scalar_pullback]
      _ = _ := box_scalar_pullback F a s hsa y
  have heqt := heq.eq_of_nhds
  obtain ⟨d, hd, hd_bound⟩ := H.scalar_time_derivative_bound a t ha y (heqt ▸ hx)
  have hdb := (hd.hasDerivAt haN).congr_of_eventuallyEq heq
  have hev := (hM04.scalar_evolution 3 _ _ (E.extended.box b).flow t hb x).hasDerivAt hbN
  rw [hev.unique hdb, heqt]
  exact hd_bound

private theorem scalarEvolution_continuousOn
    (hM04 : RicciFlowCurvatureTheory.{u})
    (G : GeneralizedRicciFlowData.{u}) (b : G.box_index)
    (x : (G.box b).carrier.carrier) :
    ContinuousOn (fun t => ((G.box b).flow.connection t).laplacian
        ((G.box b).flow.connection t).scalarCurvature x +
      2 * ((G.box b).flow.connection t).ricciNormSq x) (G.box b).interval := by
  have hJ : UniqueDiffOn ℝ (G.box b).interval :=
    uniqueDiffOn_convex (G.box b).flow.interval.convex
      ((G.box b).flow.interval.convex.nontrivial_iff_nonempty_interior.mp
        (G.box b).flow.nontrivial)
  have h := (Poincare.Geometry.RicciFlow.Harnack.scalarCurvature_contDiffOn_time
    hM04 _ (G.box b).flow x).continuousOn_derivWithin hJ (by simp)
  apply h.congr
  intro t ht
  exact ((hM04.scalar_evolution 3 _ _ (G.box b).flow t ht x).derivWithin (hJ t ht)).symm



theorem terminal_scalar_time_derivative_bound
    (hM04 : RicciFlowCurvatureTheory.{u})
    (H : SingularTimeAssumptions F T M) (E : GeneralizedFlowExtension F T)
    (b : E.extended.box_index) (hT : T ∈ (E.extended.box b).interval)
    (x : (E.extended.box b).carrier.carrier)
    (hx : H.r₀⁻¹ ^ 2 < ((E.extended.box b).flow.connection T).scalarCurvature x) :
    ∃ d : ℝ, HasDerivWithinAt
      (fun s => ((E.extended.box b).flow.connection s).scalarCurvature x) d
      (E.extended.box b).interval T ∧
      |d| ≤ H.analytic_constant * ((E.extended.box b).flow.connection T).scalarCurvature x ^ 2 := by
  refine ⟨_, hM04.scalar_evolution 3 _ _ (E.extended.box b).flow T hT x, ?_⟩
  have hevent := terminal_box_eventually H E b hT
  have hfilter : 𝓝[<] T ≤ 𝓝[(E.extended.box b).interval] T :=
    nhdsWithin_le_iff.mpr (hevent.mono fun _ ht => ht.2)
  have hscalar := (Poincare.Geometry.RicciFlow.Harnack.scalarCurvature_continuousOn_time
    hM04 _ (E.extended.box b).flow x T hT).tendsto.mono_left hfilter
  have hevolution :=
    (scalarEvolution_continuousOn hM04 E.extended b x T hT).tendsto.mono_left hfilter
  apply le_of_tendsto_of_tendsto hevolution.abs ((hscalar.pow 2).const_mul H.analytic_constant)
  filter_upwards [hevent, self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Ioi_mem_nhds (terminalTime_pos H)),
    hscalar.eventually (Ioi_mem_nhds hx)] with t ht htt ht0 htx
  exact extension_box_scalar_evolution_bound hM04 H E b ⟨ht0, htt⟩ ht.2 x htx.le

private theorem initial_box_eventually
    (H : SingularTimeAssumptions F T M) (E : GeneralizedFlowExtension F T)
    (b : E.extended.box_index) (hzero : 0 ∈ (E.extended.box b).interval) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 T ∧ t ∈ (E.extended.box b).interval := by
  obtain ⟨U, hU, heq⟩ := (E.extended.box b).relatively_open
  have hzeroU : 0 ∈ U := (heq ▸ hzero).2
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (terminalTime_pos H)),
    nhdsWithin_le_nhds (hU.mem_nhds hzeroU)] with t ht0 htT htU
  have htF : t ∈ F.interval := H.interval_exhausts_preterminal ⟨ht0.le, htT⟩
  exact ⟨⟨ht0, htT⟩, heq ▸ ⟨E.old_times htF, htU⟩⟩



theorem initial_scalar_time_derivative_bound
    (hM04 : RicciFlowCurvatureTheory.{u})
    (H : SingularTimeAssumptions F T M) (E : GeneralizedFlowExtension F T)
    (b : E.extended.box_index) (hzero : 0 ∈ (E.extended.box b).interval)
    (x : (E.extended.box b).carrier.carrier)
    (hx : H.r₀⁻¹ ^ 2 < ((E.extended.box b).flow.connection 0).scalarCurvature x) :
    ∃ d : ℝ, HasDerivWithinAt
      (fun s => ((E.extended.box b).flow.connection s).scalarCurvature x) d
      (E.extended.box b).interval 0 ∧
      |d| ≤ H.analytic_constant * ((E.extended.box b).flow.connection 0).scalarCurvature x ^ 2 := by
  refine ⟨_, hM04.scalar_evolution 3 _ _ (E.extended.box b).flow 0 hzero x, ?_⟩
  have hevent := initial_box_eventually H E b hzero
  have hfilter : 𝓝[>] (0 : ℝ) ≤ 𝓝[(E.extended.box b).interval] 0 :=
    nhdsWithin_le_iff.mpr (hevent.mono fun _ ht => ht.2)
  have hscalar := (Poincare.Geometry.RicciFlow.Harnack.scalarCurvature_continuousOn_time
    hM04 _ (E.extended.box b).flow x 0 hzero).tendsto.mono_left hfilter
  have hevolution :=
    (scalarEvolution_continuousOn hM04 E.extended b x 0 hzero).tendsto.mono_left hfilter
  apply le_of_tendsto_of_tendsto hevolution.abs
    ((hscalar.pow 2).const_mul H.analytic_constant)
  filter_upwards [hevent, hscalar.eventually (Ioi_mem_nhds hx)] with t ht htx
  exact extension_box_scalar_evolution_bound hM04 H E b ht.1 ht.2 x htx.le



theorem extension_scalar_time_derivative_bound
    (hM04 : RicciFlowCurvatureTheory.{u})
    (H : SingularTimeAssumptions F T M) (E : GeneralizedFlowExtension F T)
    (b : E.extended.box_index) (t : ℝ) (ht : t ∈ (E.extended.box b).interval)
    (x : (E.extended.box b).carrier.carrier)
    (hx : H.r₀⁻¹ ^ 2 < ((E.extended.box b).flow.connection t).scalarCurvature x) :
    ∃ d : ℝ, HasDerivWithinAt
      (fun s => ((E.extended.box b).flow.connection s).scalarCurvature x) d
      (E.extended.box b).interval t ∧
      |d| ≤ H.analytic_constant * ((E.extended.box b).flow.connection t).scalarCurvature x ^ 2 := by
  have htE : t ∈ E.extended.interval := box_time_mem E.extended b ht
  rcases E.times_subset htE with htold | htT
  · have htold' := H.interval_preterminal htold
    by_cases htzero : t = 0
    · subst t
      exact initial_scalar_time_derivative_bound hM04 H E b ht x hx
    · have htpos : 0 < t := lt_of_le_of_ne htold'.1 (Ne.symm htzero)
      exact ⟨_, hM04.scalar_evolution 3 _ _ (E.extended.box b).flow t ht x,
        extension_box_scalar_evolution_bound hM04 H E b ⟨htpos, htold'.2⟩ ht x hx.le⟩
  · have htT' : t = T := mem_singleton_iff.mp htT
    subst t
    exact terminal_scalar_time_derivative_bound hM04 H E b ht x hx

end PoincareConjecture.M32
