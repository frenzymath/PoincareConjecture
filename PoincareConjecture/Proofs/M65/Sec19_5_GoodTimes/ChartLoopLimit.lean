import PoincareConjecture.Proofs.M65.Sec19_5_GoodTimes.TangentLimit
import PoincareConjecture.Proofs.M65.Sec19_5_GoodTimes.PeriodicLoop
import PoincareConjecture.Proofs.M65.Sec19_5_GoodTimes.ProjectedC0Limit

set_option autoImplicit false

open Set Filter Bundle
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

variable {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M]

omit [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M] in

theorem m65ContinuousMap_joint_time {J : Set ℝ}
    (f : ℕ → C((J ×ˢ (univ : Set ℝ) : Set (ℝ × ℝ)), M))
    (g : C((J ×ˢ (univ : Set ℝ) : Set (ℝ × ℝ)), M))
    (h : Tendsto f atTop (𝓝 g)) {t : ℝ} (ht : t ∈ J) (x : ℝ) :
    Tendsto (fun p : ℕ × ℝ => f p.1 ⟨(t, p.2), ht, mem_univ _⟩)
      (atTop ×ˢ 𝓝 x) (𝓝 (g ⟨(t, x), ht, mem_univ _⟩)) := by
  let slice : C(ℝ, (J ×ˢ (univ : Set ℝ) : Set (ℝ × ℝ))) :=
    ⟨fun y => ⟨(t, y), ht, mem_univ _⟩, by fun_prop⟩
  have hs := ((ContinuousMap.continuous_precomp slice).tendsto g).comp h
  exact (continuous_eval.tendsto (g.comp slice, x)).comp
    ((hs.comp tendsto_fst).prodMk_nhds tendsto_snd)

omit [IsManifold (𝓡 3) ∞ M] in
private theorem slice_contMDiff {J : Set ℝ} (hJ : IsOpen J)
    {c : ℝ × ℝ → M}
    (hc : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 3) ∞ c (J ×ˢ univ))
    {t : ℝ} (ht : t ∈ J) : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 (fun x => c (t, x)) := by
  intro x
  have h := hc.contMDiffAt (x := (t, x))
    ((hJ.prod isOpen_univ).mem_nhds ⟨ht, mem_univ x⟩)
  have hs : ContDiff ℝ ∞ (fun y : ℝ => (t, y)) := contDiff_const.prodMk contDiff_id
  exact (h.comp x hs.contMDiff.contMDiffAt).of_le (by simp)

private theorem slice_deriv_jet {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : ℝ × ℝ → V} {t x : ℝ} (hf : DifferentiableAt ℝ f (t, x)) :
    deriv (fun y => f (t, y)) x =
      iteratedFDeriv ℝ 1 f (t, x) (fun _ => (0, 1)) := by
  rw [iteratedFDeriv_one_apply]
  exact (hf.hasFDerivAt.comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))).hasDerivAt.deriv

set_option maxHeartbeats 800000 in

theorem m65C1Loop_tendsto_of_local_chart_jets
    {J : Set ℝ} (hJ : IsOpen J) (c : ℕ → ℝ × ℝ → M) (c0 : ℝ × ℝ → M)
    (hc : ∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 3) ∞ (c k) (J ×ˢ univ))
    (hc0 : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 3) ∞ c0 (J ×ˢ univ))
    (hbase : ∀ t ∈ J, ∀ x, Tendsto (fun p : ℕ × ℝ => c p.1 (t, p.2))
      (atTop ×ˢ 𝓝 x) (𝓝 (c0 (t, x))))
    (hchart : ∀ z ∈ J ×ˢ (univ : Set ℝ), ∃ (p : M) (U V : Set ℝ),
      IsOpen U ∧ IsOpen V ∧ z.1 ∈ U ∧ z.2 ∈ V ∧ U ×ˢ V ⊆ J ×ˢ univ ∧
      (∀ w ∈ U ×ˢ V, c0 w ∈ (chartAt LoopAmbient p).source) ∧
      ∀ K, IsCompact K → K ⊆ U ×ˢ V → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ 1 (fun w => (chartAt LoopAmbient p) (c k w)))
        (iteratedFDeriv ℝ 1 (fun w => (chartAt LoopAmbient p) (c0 w))) atTop K)
    {t : ℝ} (ht : t ∈ J) (loops : ℕ → C1FreeLoopSpace (M := M))
    (gamma : C1FreeLoopSpace (M := M))
    (hloops : ∀ k x, periodicFreeLoop (loops k) x = c k (t, x))
    (hgamma : ∀ x, periodicFreeLoop gamma x = c0 (t, x)) :
    Tendsto loops atTop (𝓝 gamma) := by
  have hΩ : IsOpen (J ×ˢ (univ : Set ℝ)) := hJ.prod isOpen_univ
  have hvalue (x : ℝ) := hbase t ht x
  apply m65C1Loop_tendsto_of_angular loops gamma
  · intro x
    simpa only [hloops, hgamma] using hvalue x
  intro x
  have hvel : Tendsto (fun q : ℕ × ℝ =>
      (⟨c q.1 (t, q.2), curveVelocity (fun y => c q.1 (t, y)) q.2⟩ :
        TangentBundle (𝓡 3) M)) (atTop ×ˢ 𝓝 x)
      (𝓝 (⟨c0 (t, x), curveVelocity (fun y => c0 (t, y)) x⟩ :
        TangentBundle (𝓡 3) M)) := by
    obtain ⟨p, U, V, hU, hV, htU, hxV, hUV, hsource, hjet⟩ :=
      hchart (t, x) ⟨ht, mem_univ x⟩
    have h0 := hsource (t, x) ⟨htU, hxV⟩
    apply m65CurveTangent_tendsto_of_chart (fun k y => c k (t, y))
      (fun y => c0 (t, y)) (fun k => slice_contMDiff hJ (hc k) ht)
      (slice_contMDiff hJ hc0 ht) x p h0 (hvalue x)
    have hs0 : ContDiffAt ℝ ∞ (fun w => (chartAt LoopAmbient p) (c0 w)) (t, x) :=
      ((contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) h0).comp
        (t, x) (hc0.contMDiffAt (hΩ.mem_nhds ⟨ht, mem_univ x⟩))).contDiffAt
    obtain ⟨K, hK, hxK, hKUV⟩ := exists_compact_subset (hU.prod hV) ⟨htU, hxV⟩
    have hj : TendstoUniformlyOn
        (fun q : ℕ × ℝ => iteratedFDeriv ℝ 1
          (fun w => (chartAt LoopAmbient p) (c q.1 w)))
        (iteratedFDeriv ℝ 1 (fun w => (chartAt LoopAmbient p) (c0 w)))
        (atTop ×ˢ 𝓝 x) K := by
      intro W hW
      exact tendsto_fst.eventually (hjet K hK hKUV W hW)
    have harg : Tendsto (fun q : ℕ × ℝ => (t, q.2))
        (atTop ×ˢ 𝓝 x) (𝓝[K] (t, x)) := by
      rw [nhdsWithin_eq_nhds.mpr (mem_interior_iff_mem_nhds.mp hxK)]
      exact tendsto_const_nhds.prodMk_nhds tendsto_snd
    have hlim := hj.tendsto_comp
      (hs0.continuousAt_iteratedFDeriv (by simp)).continuousWithinAt harg
    have happ := ((continuous_eval_const (fun _ => (0, 1))).tendsto _).comp hlim
    rw [slice_deriv_jet (hs0.differentiableAt (by simp))]
    apply happ.congr'
    have hsrc := (hvalue x).eventually ((chartAt LoopAmbient p).open_source.mem_nhds h0)
    filter_upwards [hsrc] with q hq
    have hs : ContDiffAt ℝ ∞ (fun w => (chartAt LoopAmbient p) (c q.1 w)) (t, q.2) :=
      ((contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hq).comp
        (t, q.2) ((hc q.1).contMDiffAt (hΩ.mem_nhds ⟨ht, mem_univ q.2⟩))).contDiffAt
    exact (slice_deriv_jet (hs.differentiableAt (by simp))).symm
  have hl (k : ℕ) : periodicFreeLoop (loops k) = fun y => c k (t, y) := funext (hloops k)
  have hg : periodicFreeLoop gamma = fun y => c0 (t, y) := funext hgamma
  convert hvel using 1
  · funext p
    exact congrArg (fun f : ℝ → M =>
      (⟨f p.2, curveVelocity f p.2⟩ : TangentBundle (𝓡 3) M)) (hl p.1)
  · exact congrArg (fun f : ℝ → M =>
      𝓝 (⟨f x, curveVelocity f x⟩ : TangentBundle (𝓡 3) M)) hg

end PoincareConjecture
