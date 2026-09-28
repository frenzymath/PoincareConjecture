import PoincareConjecture.Proofs.M28.Generalized.CompactPathTransport

set_option autoImplicit false

open Set Function Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

theorem exists_good_slice_path
    (F : GeneralizedRicciFlowData.{u}) (P : RicciFlowCurvatureTheory.{u})
    {epsilon C t : ℝ} (htF : t ∈ F.interval) (x : (F.slice t).carrier)
    (hdense : generalizedEarlierDenseStrongCanonicalNeighborhoods F epsilon C t x)
    (γ : ℝ → (F.slice t).carrier) (hγ : ContMDiff 𝓘(ℝ) (𝓡 3) 1 γ)
    {Rstart Rend L : ℝ}
    (hstart : F.scalar ⟨t, γ 0⟩ < Rstart)
    (hend : Rend < F.scalar ⟨t, γ 1⟩)
    (hlength : (F.metric t).pathELength γ 0 1 < ENNReal.ofReal L) :
    ∃ s, s ∈ F.interval ∧ ∃ η : ℝ → (F.slice s).carrier,
      ContMDiffOn 𝓘(ℝ) (𝓡 3) 1 η (Icc 0 1) ∧
      F.scalar ⟨s, η 0⟩ < Rstart ∧ Rend < F.scalar ⟨s, η 1⟩ ∧
      (F.metric s).pathELength η 0 1 < ENNReal.ofReal L ∧
      generalizedSliceStrongCanonicalNeighborhoods F epsilon C (4 * F.scalar ⟨t, x⟩) s := by
  obtain ⟨δ, hδ, Γ, hΓ, hΓt, hscalar, hlen⟩ :=
    exists_compact_path_transport F P t htF γ hγ
  let J := F.interval ∩ Ioo (t - δ) (t + δ)
  have htJ : t ∈ J := ⟨htF, by constructor <;> linarith⟩
  let tJ : J := ⟨t, htJ⟩
  have h0 : Continuous (fun s : J => F.scalar ⟨s.val, Γ s 0⟩) :=
    hscalar.comp (f := fun s : J => (s, (0 : unitInterval)))
      (continuous_id.prodMk continuous_const)
  have h1 : Continuous (fun s : J => F.scalar ⟨s.val, Γ s 1⟩) :=
    hscalar.comp (f := fun s : J => (s, (1 : unitInterval)))
      (continuous_id.prodMk continuous_const)
  have ht0 : F.scalar ⟨tJ.val, Γ tJ 0⟩ < Rstart := by
    simpa only [tJ, hΓt htJ 0 ⟨le_rfl, zero_le_one⟩] using hstart
  have ht1 : Rend < F.scalar ⟨tJ.val, Γ tJ 1⟩ := by
    simpa only [tJ, hΓt htJ 1 ⟨zero_le_one, le_rfl⟩] using hend
  have htlen : (F.metric tJ.val).pathELength (Γ tJ) 0 1 < ENNReal.ofReal L := by
    have heq : (F.metric t).pathELength (Γ tJ) 0 1 =
        (F.metric t).pathELength γ 0 1 := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : (F.slice t).carrier → Type _) :=
        ⟨(F.metric t).toRiemannianMetric⟩
      exact Manifold.pathELength_congr (hΓt htJ)
    exact heq.trans_lt hlength
  have hevent : ∀ᶠ s : J in 𝓝 tJ,
      F.scalar ⟨s.val, Γ s 0⟩ < Rstart ∧ Rend < F.scalar ⟨s.val, Γ s 1⟩ ∧
      (F.metric s.val).pathELength (Γ s) 0 1 < ENNReal.ofReal L :=
    (h0.continuousAt.eventually_lt_const ht0).and
      ((h1.continuousAt.eventually_const_lt ht1).and
        (hlen.continuousAt.eventually_lt_const htlen))
  obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp hevent
  have hmin : 0 < min δ ε := lt_min hδ hε
  obtain ⟨s, hsF, hslow, hst, hgood⟩ :=
    hdense t htF le_rfl (t - min δ ε) (by linarith)
  have hsJ : s ∈ J := by
    refine ⟨hsF, ?_, ?_⟩
    · linarith [min_le_left δ ε]
    · linarith
  have hdist : dist (⟨s, hsJ⟩ : J) tJ < ε := by
    change |s - t| < ε
    rw [abs_of_nonpos (sub_nonpos.mpr hst)]
    linarith [min_le_right δ ε]
  obtain ⟨hs0, hs1, hslen⟩ := hnear hdist
  exact ⟨s, hsF, Γ ⟨s, hsJ⟩, hΓ _, hs0, hs1, hslen, hgood⟩

end PoincareConjecture.M28
