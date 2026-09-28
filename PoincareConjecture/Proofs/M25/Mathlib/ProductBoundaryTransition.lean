import PoincareConjecture.Proofs.M25.Mathlib.RealPartialDerivative
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.OpenPartialHomeomorph.Composition

set_option autoImplicit false
open Set
open scoped Manifold ContDiff Topology
universe u v w u' v' w'
namespace OpenPartialHomeomorph
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] {K : Type w} [TopologicalSpace K]
  [ChartedSpace H K] [IsManifold I ∞ K] [CompactSpace K]
  {E' : Type u'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type v'} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {M : Type w'} [TopologicalSpace M] [ChartedSpace H' M]
  [IsManifold J ∞ M]

set_option linter.unusedSectionVars false in

theorem exists_positive_scalar_boundary_transition
    (e f : OpenPartialHomeomorph (K × ℝ) M)
    (he : univ ×ˢ Icc (0 : ℝ) 1 ⊆ e.source)
    (hf : univ ×ˢ Icc (0 : ℝ) 1 ⊆ f.source)
    (hes : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) J ∞ e e.source)
    (hei : ContMDiffOn J (I.prod 𝓘(ℝ, ℝ)) ∞ e.symm e.target)
    (hfs : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) J ∞ f f.source)
    (hfi : ContMDiffOn J (I.prod 𝓘(ℝ, ℝ)) ∞ f.symm f.target)
    (hboundary : range (fun q : K => e (q, 1)) =
      range (fun q : K => f (q, 0)))
    (hinter : (e '' (univ ×ˢ Icc (0 : ℝ) 1)) ∩
        (f '' (univ ×ˢ Icc (0 : ℝ) 1)) =
      range (fun q : K => f (q, 0))) :
    ∃ r : ℝ, 0 < r ∧ r < 1 / 4 ∧
      univ ×ˢ Ioo (1 - r) (1 + r) ⊆ (e.trans f.symm).source ∧
      (∀ q : K, (f.symm (e (q, 1))).2 = 0) ∧
      (∀ q : K, ∀ s ∈ Ioo (1 - r) (1 + r),
        0 < deriv (fun t : ℝ => (f.symm (e (q, t))).2) s) := by
  let T : OpenPartialHomeomorph (K × ℝ) (K × ℝ) := e.trans f.symm
  let k : K × ℝ → ℝ := fun z => (T z).2
  let d : K × ℝ → ℝ := fun z => deriv (fun t : ℝ => k (z.1, t)) z.2
  have he1 (q : K) : (q, (1 : ℝ)) ∈ e.source :=
    he ⟨mem_univ _, ⟨by norm_num, le_rfl⟩⟩
  have hf0 (q : K) : (q, (0 : ℝ)) ∈ f.source :=
    hf ⟨mem_univ _, ⟨le_rfl, by norm_num⟩⟩
  have hb (q : K) : ∃ p : K, f (p, 0) = e (q, 1) := by
    have h : e (q, 1) ∈ range (fun p : K => f (p, 0)) := by
      rw [← hboundary]
      exact ⟨q, rfl⟩
    exact h
  have hsource (q : K) : (q, (1 : ℝ)) ∈ T.source := by
    obtain ⟨p, hp⟩ := hb q
    refine ⟨he1 q, ?_⟩
    change e (q, 1) ∈ f.target
    rw [← hp]
    exact f.map_source (hf0 p)
  have hzero (q : K) : k (q, 1) = 0 := by
    obtain ⟨p, hp⟩ := hb q
    change (f.symm (e (q, 1))).2 = 0
    rw [← hp, f.left_inv (hf0 p)]
  have hTs : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞
      T T.source :=
    hfi.comp (hes.mono (fun _ hz => hz.1)) (fun _ hz => hz.2)
  have hTi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞
      T.symm T.target :=
    hei.comp (hfs.mono (fun _ hz => hz.1)) (fun _ hz => hz.2)
  have hTm : T.MDifferentiable (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) :=
    ⟨hTs.mdifferentiableOn (by simp), hTi.mdifferentiableOn (by simp)⟩
  have hks : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ k T.source :=
    contMDiff_snd.comp_contMDiffOn hTs
  have hds : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ d T.source := by
    intro z hz
    exact ((hks.contMDiffAt (T.open_source.mem_nhds hz)).real_partial_deriv_snd).contMDiffWithinAt
  have hdne (q : K) : d (q, 1) ≠ 0 := by
    intro hd0
    obtain ⟨v, hv⟩ := hTm.mfderiv_surjective (hsource q) ((0 : E), (1 : ℝ))
    have hhor : (fun p : K => k (p, 1)) = fun _ => (0 : ℝ) := funext hzero
    have hvis : deriv (fun t : ℝ => k (q, t)) 1 = 0 := hd0
    have hsplit := mfderiv_prod_eq_add_apply
      (I := I) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓘(ℝ, ℝ))
      (p := (q, (1 : ℝ))) (v := v)
      ((hks.contMDiffAt (T.open_source.mem_nhds (hsource q))).mdifferentiableAt (by simp))
    change mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) k (q, 1) v =
      mfderiv I 𝓘(ℝ, ℝ) (fun p : K => k (p, 1)) q v.1 +
        mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => k (q, t)) 1 v.2 at hsplit
    have hhorv : mfderiv I 𝓘(ℝ, ℝ) (fun p : K => k (p, 1)) q v.1 = 0 := by
      rw [hhor, mfderiv_const]
      rfl
    have hvisv : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => k (q, t)) 1 v.2 = 0 := by
      rw [mfderiv_eq_fderiv]
      change (fderiv ℝ (fun t : ℝ => k (q, t)) 1 : ℝ →L[ℝ] ℝ) (v.2 : ℝ) = 0
      rw [fderiv_eq_smul_deriv, hvis, smul_zero]
    rw [hhorv, hvisv, zero_add] at hsplit
    have hchain := mfderiv_comp_apply
      (I := I.prod 𝓘(ℝ, ℝ)) (I' := I.prod 𝓘(ℝ, ℝ)) (I'' := 𝓘(ℝ, ℝ))
      (q, (1 : ℝ)) (g := Prod.snd) mdifferentiableAt_snd
      (hTm.mdifferentiableAt (hsource q)) v
    rw [mfderiv_snd] at hchain
    change mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) k (q, 1) v =
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) T (q, 1) v).2 at hchain
    rw [hv] at hchain
    have hbad : (0 : ℝ) = 1 := hsplit.symm.trans hchain
    exact zero_ne_one hbad
  have hdpos (q : K) : 0 < d (q, 1) := by
    by_contra hpos
    have hneg : d (q, 1) < 0 := lt_of_le_of_ne (le_of_not_gt hpos) (hdne q)
    let O : Set (K × ℝ) :=
      (T.source ∩ d ⁻¹' Iio 0) ∩ (T.source ∩ k ⁻¹' Iio 1)
    have hO : IsOpen O :=
      (hds.continuousOn.isOpen_inter_preimage T.open_source isOpen_Iio).inter
        (hks.continuousOn.isOpen_inter_preimage T.open_source isOpen_Iio)
    have hqO : (q, (1 : ℝ)) ∈ O :=
      ⟨⟨hsource q, hneg⟩, hsource q, by change k (q, 1) < 1; rw [hzero]; norm_num⟩
    obtain ⟨a, b, h1, hI⟩ := mem_nhds_iff_exists_Ioo_subset.mp
      ((hO.preimage (continuous_const.prodMk continuous_id)).mem_nhds hqO)
    have hlocal (t : ℝ) (ht : t ∈ Ioo a b) :
        (q, t) ∈ T.source ∧ d (q, t) < 0 ∧ k (q, t) < 1 := by
      have h := hI ht
      exact ⟨h.1.1, h.1.2, h.2.2⟩
    have hcont : ContinuousOn (fun t : ℝ => k (q, t)) (Ioo a b) :=
      hks.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun t ht => (hlocal t ht).1)
    have hanti : StrictAntiOn (fun t : ℝ => k (q, t)) (Ioo a b) := by
      apply strictAntiOn_of_deriv_neg (convex_Ioo a b) hcont
      intro t ht
      exact (hlocal t (by simpa only [interior_Ioo] using ht)).2.1
    obtain ⟨s, hslow, hs1⟩ := exists_between (show max a (0 : ℝ) < 1 by
      exact max_lt h1.1 (by norm_num))
    have hsa : a < s := lt_of_le_of_lt (le_max_left _ _) hslow
    have hs0 : 0 < s := lt_of_le_of_lt (le_max_right _ _) hslow
    have hsI : s ∈ Ioo a b := ⟨hsa, hs1.trans h1.2⟩
    have hkpos : 0 < k (q, s) := by
      simpa only [hzero] using hanti hsI h1 hs1
    have hsp := (hlocal s hsI).1
    have hboth : e (q, s) ∈ (e '' (univ ×ˢ Icc (0 : ℝ) 1)) ∩
        (f '' (univ ×ˢ Icc (0 : ℝ) 1)) := by
      refine ⟨⟨(q, s), ⟨mem_univ _, hs0.le, hs1.le⟩, rfl⟩, ?_⟩
      refine ⟨f.symm (e (q, s)), ⟨mem_univ _, hkpos.le, (hlocal s hsI).2.2.le⟩,
        f.right_inv hsp.2⟩
    rw [hinter] at hboth
    obtain ⟨p, hp⟩ := hboth
    have hbad : k (q, s) = 0 := by
      change (f.symm (e (q, s))).2 = 0
      rw [← hp, f.left_inv (hf0 p)]
    linarith
  have hO : IsOpen (T.source ∩ d ⁻¹' Ioi 0) :=
    hds.continuousOn.isOpen_inter_preimage T.open_source isOpen_Ioi
  have hboundaryO : (univ : Set K) ×ˢ {(1 : ℝ)} ⊆ T.source ∩ d ⁻¹' Ioi 0 := by
    rintro ⟨q, t⟩ ⟨_, ht⟩
    have ht1 : t = 1 := ht
    subst t
    exact ⟨hsource q, hdpos q⟩
  obtain ⟨U, V, _, hV, hU, hV1, hUV⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hO hboundaryO
  obtain ⟨a, b, h1, hI⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp
      (hV.mem_nhds (hV1 (show (1 : ℝ) ∈ {(1 : ℝ)} from rfl)))
  have hc : 0 < min (1 / 4 : ℝ) (min (1 - a) (b - 1)) :=
    lt_min (by norm_num) (lt_min (by linarith [h1.1]) (by linarith [h1.2]))
  obtain ⟨r, hr0, hr⟩ := exists_between hc
  obtain ⟨hr4, hrab⟩ := lt_min_iff.mp hr
  obtain ⟨hra, hrb⟩ := lt_min_iff.mp hrab
  have hstrip (s : ℝ) (hs : s ∈ Ioo (1 - r) (1 + r)) : s ∈ V :=
    hI ⟨by linarith [hs.1], by linarith [hs.2]⟩
  refine ⟨r, hr0, hr4, ?_, hzero, ?_⟩
  · intro z hz
    exact (hUV ⟨hU (mem_univ z.1), hstrip z.2 hz.2⟩).1
  · intro q s hs
    have hp : (q, s) ∈ T.source ∩ d ⁻¹' Ioi 0 :=
      hUV ⟨hU (mem_univ q), hstrip s hs⟩
    exact hp.2

end OpenPartialHomeomorph
