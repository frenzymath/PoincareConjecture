import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace OpenPartialHomeomorph

theorem exists_fiberwise_transition_band
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    {K : Type*} [TopologicalSpace K] [ChartedSpace H K]
    [PreconnectedSpace K]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
    (e f : OpenPartialHomeomorph (K × ℝ) M) (A : K ≃ₜ K)
    {a b : ℝ} (hab : a < b)
    (hsource : univ ×ˢ Icc a b ⊆ e.source)
    (htarget : MapsTo e (univ ×ˢ Icc a b) f.target)
    (hfirst : ∀ z : K × ℝ, z.2 ∈ Icc a b →
      (f.symm (e z)).1 = A z.1)
    (he : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) J ∞ e e.source)
    (hei : ContMDiffOn J (I.prod 𝓘(ℝ, ℝ)) ∞ e.symm e.target)
    (hf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) J ∞ f f.source)
    (hfi : ContMDiffOn J (I.prod 𝓘(ℝ, ℝ)) ∞ f.symm f.target) :
    let h : K × ℝ → ℝ := fun z => (f.symm (e z)).2
    let T := (e.restr (univ ×ˢ Ioo a b)).trans f.symm
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      (∀ q : K, StrictMonoOn (fun s => σ * h (q, s)) (Icc a b)) ∧
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun q : K => h (q, a)) ∧
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun q : K => h (q, b)) ∧
      T.source = univ ×ˢ Ioo a b ∧
      T.target = {z : K × ℝ |
        σ * h (A.symm z.1, a) < σ * z.2 ∧
          σ * z.2 < σ * h (A.symm z.1, b)} ∧
      T.target ⊆ f.source ∧
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞ T T.source ∧
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞ T.symm T.target ∧
      (∀ z ∈ T.source,
        T z = (A z.1, h z) ∧ f (T z) = e z) ∧
      (∀ z ∈ T.target,
        T.symm z = e.symm (f z) ∧
          (T.symm z).1 = A.symm z.1 ∧ e (T.symm z) = f z) := by
  let h : K × ℝ → ℝ := fun z => (f.symm (e z)).2
  let T := (e.restr (univ ×ˢ Ioo a b)).trans f.symm
  have hclosed {z : K × ℝ} (hz : z ∈ univ ×ˢ Ioo a b) :
      z ∈ univ ×ˢ Icc a b := ⟨hz.1, hz.2.1.le, hz.2.2.le⟩
  have hTsource : T.source = univ ×ˢ Ioo a b := by
    dsimp only [T]
    rw [trans_source, e.restr_source' _ (isOpen_univ.prod isOpen_Ioo), symm_source]
    ext z
    change ((z ∈ e.source ∧ z ∈ univ ×ˢ Ioo a b) ∧ e z ∈ f.target) ↔
      z ∈ univ ×ˢ Ioo a b
    constructor
    · exact fun hz => hz.1.2
    · intro hz
      exact ⟨⟨hsource (hclosed hz), hz⟩, htarget (hclosed hz)⟩
  have hTclosed {z : K × ℝ} (hz : z ∈ T.source) : z ∈ univ ×ˢ Icc a b :=
    hclosed (hTsource ▸ hz)
  have hTtarget_mem (z : K × ℝ) (hz : z ∈ T.target) :
      z ∈ f.source ∧ f z ∈ e.target := by
    change z ∈ f.source ∧ f z ∈ (e.restr (univ ×ˢ Ioo a b)).target at hz
    exact ⟨hz.1, hz.2.1⟩
  have hTpair (z : K × ℝ) (hz : z.2 ∈ Icc a b) : T z = (A z.1, h z) :=
    Prod.ext (hfirst z hz) rfl
  have hslice (t : ℝ) (ht : t ∈ Icc a b) :
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun q : K => h (q, t)) := by
    have hp : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞ (fun q : K => (q, t)) :=
      contMDiff_id.prodMk contMDiff_const
    have heq : ContMDiff I J ∞ (fun q : K => e (q, t)) :=
      he.comp_contMDiff hp (fun q => hsource ⟨mem_univ q, ht⟩)
    have hcoord : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun q : K => f.symm (e (q, t))) :=
      hfi.comp_contMDiff heq (fun q => htarget ⟨mem_univ q, ht⟩)
    exact contMDiff_snd.comp hcoord
  have hcont (q : K) : ContinuousOn (fun t : ℝ => h (q, t)) (Icc a b) := by
    have hp : Continuous (fun t : ℝ => (q, t)) := continuous_const.prodMk continuous_id
    have heq : ContinuousOn (fun t : ℝ => e (q, t)) (Icc a b) :=
      e.continuousOn.comp hp.continuousOn (fun _ ht => hsource ⟨mem_univ q, ht⟩)
    exact (f.symm.continuousOn.comp heq
      (fun _ ht => htarget ⟨mem_univ q, ht⟩)).snd
  have hinj (q : K) : InjOn (fun t : ℝ => h (q, t)) (Icc a b) := by
    intro s hs t ht hst
    have hp : f.symm (e (q, s)) = f.symm (e (q, t)) :=
      Prod.ext ((hfirst (q, s) hs).trans (hfirst (q, t) ht).symm) hst
    have heq := congrArg f hp
    rw [f.right_inv (htarget ⟨mem_univ q, hs⟩),
      f.right_inv (htarget ⟨mem_univ q, ht⟩)] at heq
    exact congrArg Prod.snd (e.injOn (hsource ⟨mem_univ q, hs⟩)
      (hsource ⟨mem_univ q, ht⟩) heq)
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  let d : K → ℝ := fun q => h (q, b) - h (q, a)
  have hd : Continuous d := (hslice b hb).continuous.sub (hslice a ha).continuous
  have hdne (q : K) (_ : q ∈ (univ : Set K)) : d q ≠ 0 := by
    intro hz
    have heq : h (q, a) = h (q, b) := (sub_eq_zero.mp hz).symm
    exact hab.ne (hinj q ha hb heq)
  have hsign : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∀ q : K, σ * h (q, a) < σ * h (q, b) := by
    rcases isPreconnected_univ.mapsTo_Ioi_or_Iio hd.continuousOn hdne with hpos | hneg
    · refine ⟨1, Or.inl rfl, ?_⟩
      intro q
      have hq : 0 < h (q, b) - h (q, a) := hpos (mem_univ q)
      simpa only [one_mul] using sub_pos.mp hq
    · refine ⟨-1, Or.inr rfl, ?_⟩
      intro q
      have hq : h (q, b) - h (q, a) < 0 := hneg (mem_univ q)
      simpa only [neg_one_mul] using neg_lt_neg (sub_neg.mp hq)
  obtain ⟨σ, hσ, hend⟩ := hsign
  have hσne : σ ≠ 0 := by
    rcases hσ with rfl | rfl
    · exact one_ne_zero
    · exact neg_ne_zero.mpr one_ne_zero
  have hsigcont (q : K) :
      ContinuousOn (fun s => σ * h (q, s)) (Icc a b) :=
    continuousOn_const.mul (hcont q)
  have hmono (q : K) : StrictMonoOn (fun s => σ * h (q, s)) (Icc a b) :=
    ContinuousOn.strictMonoOn_of_injOn_Icc hab.le (hend q).le (hsigcont q)
      (fun _ hs _ ht hst => hinj q hs ht (mul_left_cancel₀ hσne hst))
  have hTtarget : T.target = {z : K × ℝ |
      σ * h (A.symm z.1, a) < σ * z.2 ∧
        σ * z.2 < σ * h (A.symm z.1, b)} := by
    rw [← T.image_source_eq_target]
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hwopen : w.2 ∈ Ioo a b := (hTsource ▸ hw).2
      have hwclosed : w.2 ∈ Icc a b := ⟨hwopen.1.le, hwopen.2.le⟩
      change σ * h (A.symm (T w).1, a) < σ * (T w).2 ∧
        σ * (T w).2 < σ * h (A.symm (T w).1, b)
      rw [hTpair w hwclosed]
      simp only [A.symm_apply_apply]
      exact ⟨hmono w.1 ha hwclosed hwopen.1, hmono w.1 hwclosed hb hwopen.2⟩
    · intro hz
      change σ * h (A.symm z.1, a) < σ * z.2 ∧
        σ * z.2 < σ * h (A.symm z.1, b) at hz
      let q := A.symm z.1
      have himage := (hsigcont q).image_Ioo_of_strictMonoOn hab.le (hmono q)
      have hzimage : σ * z.2 ∈ (fun s => σ * h (q, s)) '' Ioo a b := by
        rw [himage]
        exact hz
      obtain ⟨s, hs, heq⟩ := hzimage
      refine ⟨(q, s), ?_, ?_⟩
      · rw [hTsource]
        exact ⟨mem_univ q, hs⟩
      · rw [hTpair (q, s) ⟨hs.1.le, hs.2.le⟩]
        apply Prod.ext
        · exact A.apply_symm_apply z.1
        · exact mul_left_cancel₀ hσne heq
  have hTs : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞ T T.source :=
    hfi.comp (he.mono (fun _ hz => hsource (hTclosed hz)))
      (fun _ hz => htarget (hTclosed hz))
  have hTis : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞ T.symm T.target :=
    hei.comp (hf.mono (fun z hz => (hTtarget_mem z hz).1))
      (fun z hz => (hTtarget_mem z hz).2)
  refine ⟨σ, hσ, hmono, hslice a ha, hslice b hb, hTsource, hTtarget,
    (fun z hz => (hTtarget_mem z hz).1), hTs, hTis, ?_, ?_⟩
  · intro z hz
    exact ⟨hTpair z (hTclosed hz).2, f.right_inv (htarget (hTclosed hz))⟩
  · intro z hz
    refine ⟨rfl, ?_, ?_⟩
    · have hw : (T.symm z).2 ∈ Icc a b := (hTclosed (T.map_target hz)).2
      have hbase : A (T.symm z).1 = z.1 := by
        have heq := T.right_inv hz
        rw [hTpair (T.symm z) hw] at heq
        exact congrArg Prod.fst heq
      calc
        (T.symm z).1 = A.symm (A (T.symm z).1) := (A.symm_apply_apply _).symm
        _ = A.symm z.1 := congrArg A.symm hbase
    · exact e.right_inv (hTtarget_mem z hz).2

end OpenPartialHomeomorph
