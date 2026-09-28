import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusC2BoundaryMotion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem m64C2ShrinkingCurve_free_relabel_smooth_near_anchor
    (F : RicciFlow n M (Icc a b)) {c : ℝ → ℝ → M}
    (hc : M63C2ShrinkingCurveOn F c (Icc a b)) {t : ℝ} (ht : t ∈ Ioo a b)
    {sigma : ℝ → ℝ} (hsigma : Continuous sigma)
    (hanchor : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun x => c (sigma x) t)) :
    ∃ tau s : ℝ, a < tau ∧ tau < t ∧ t < s ∧ s < b ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
        (fun q : ℝ × ℝ => c (sigma q.1) q.2) (univ ×ˢ Ioo tau s) := by
  let : Nonempty M := ⟨c 0 t⟩
  have hi := M63.c2ShrinkingCurve_intrinsic_regularity F isCompact_univ
    (ht.1.trans ht.2) le_rfl (Or.inl rfl) hc
  let tau := (a + t) / 2
  let s := (t + b) / 2
  have hat : a < tau := by dsimp only [tau]; linarith [ht.1]
  have htt : tau < t := by dsimp only [tau]; linarith [ht.1]
  have hts : t < s := by dsimp only [s]; linarith [ht.2]
  have hsb : s < b := by dsimp only [s]; linarith [ht.2]
  have hslab : Icc tau s ⊆ Icc a b := Icc_subset_Icc hat.le hsb.le
  obtain ⟨phi, d, hphi, _hbij, _hpos, _hshift, hd, hdslices, hrel⟩ :=
    M63.exists_fixed_smooth_relabeling F isCompact_univ hc hi hat (htt.trans hts) hslab
  obtain ⟨N, e, he, hemb, hinj⟩ := exists_embedding_euclidean_of_compact (I := 𝓡 n) (M := M)
  obtain ⟨U, rho, hU, heU, hrho, hrhoe, _hmin, _huniq⟩ :=
    M63.exists_smooth_compact_embedded_retraction e hemb he hinj
  have htJ : t ∈ Icc tau s := ⟨htt.le, hts.le⟩
  let f : ℝ → EuclideanSpace ℝ (Fin N) := fun y => e (d y t)
  have hf : ContDiff ℝ ∞ f := (he.comp (hdslices t htJ)).contDiff
  have hdata := (M63.c2ShrinkingCurve_embedded_closed_data hd.1 he).2.1
  have hleft := (M63.smooth_retraction_differentials he hU heU hrho hrhoe).2.2
  have hne (y : ℝ) : deriv f y ≠ 0 := by
    have hder : HasDerivAt f
        (mfderiv (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) e (d y t)
          (curveVelocity (n := n) (fun z => d z t) y)) y := hdata t htJ y
    rw [hder.deriv]
    intro hz
    have h := hleft (d y t) (curveVelocity (n := n) (fun z => d z t) y)
    erw [hz, map_zero] at h
    exact hd.1.immersed t htJ y h.symm
  let psi := phi ∘ sigma
  have hpsi : Continuous psi := hphi.continuous.comp hsigma
  have hfc : ContDiff ℝ ∞ (f ∘ psi) := by
    have heq : f ∘ psi = fun x => e (c (sigma x) t) :=
      funext fun x => congrArg e (hrel t htJ (sigma x)).symm
    rw [heq]
    exact (he.comp hanchor).contDiff
  have hpsis : ContDiff ℝ ∞ psi := contDiff_iff_contDiffAt.mpr fun x =>
    M63.contDiffAt_of_comp_immersed_curve (by simp) hpsi.continuousAt
      hf.contDiffAt (hne (psi x)) hfc.contDiffAt
  have hmap : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun q : ℝ × ℝ => (psi q.1, q.2)) :=
    ((hpsis.comp contDiff_fst).prodMk contDiff_snd).contMDiff
  have hdlocal : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun q : ℝ × ℝ => d q.1 q.2) (univ ×ˢ Ioo tau s) := by
    simpa only [interior_Icc] using hd.2
  refine ⟨tau, s, hat, htt, hts, hsb, ?_⟩
  apply (hdlocal.comp hmap.contMDiffOn (fun q hq => ⟨mem_univ _, hq.2⟩)).congr
  intro q hq
  exact hrel q.2 (Ioo_subset_Icc_self hq.2) (sigma q.1)

theorem m64C2ShrinkingCurve_exists_free_centered_motion
    (F : RicciFlow n M (Icc a b)) {c : ℝ → ℝ → M}
    (hc : M63C2ShrinkingCurveOn F c (Icc a b)) {t : ℝ} (ht : t ∈ Ioo a b)
    {sigma : ℝ → ℝ} (hsigma : Continuous sigma)
    (hshift_sigma : ∀ x, sigma (x + curvePeriod) = sigma x + curvePeriod)
    (hanchor : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun x => c (sigma x) t)) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ f : ℝ → ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞ (fun q => f q.1 q.2)
        (Ioo (-epsilon) epsilon ×ˢ univ) ∧
      (∀ z x, f z (x + curvePeriod) = f z x) ∧
      (∀ z ∈ Ioo (-epsilon) epsilon, ∀ x, f z x = c (sigma x) (t + z)) ∧
      ∀ x, curveVelocity (fun z => f z x) 0 = m62CurvatureVector F c t (sigma x) := by
  classical
  obtain ⟨tau, s, hat, htt, hts, hsb, hjoint⟩ :=
    m64C2ShrinkingCurve_free_relabel_smooth_near_anchor F hc ht hsigma hanchor
  let epsilon := min (t - tau) (s - t) / 2
  have hepsilon : 0 < epsilon :=
    half_pos (lt_min (sub_pos.mpr htt) (sub_pos.mpr hts))
  have hshift (z : ℝ) (hz : z ∈ Ioo (-epsilon) epsilon) : t + z ∈ Ioo tau s := by
    dsimp only [epsilon] at hz
    constructor <;>
      linarith [min_le_left (t - tau) (s - t), min_le_right (t - tau) (s - t),
        hz.1, hz.2]
  have hshift_full (z : ℝ) (hz : z ∈ Ioo (-epsilon) epsilon) : t + z ∈ Icc a b :=
    ⟨(hat.trans (hshift z hz).1).le, ((hshift z hz).2.trans hsb).le⟩
  let f : ℝ → ℝ → M :=
    fun z x => c (sigma x) (if t + z ∈ Icc a b then t + z else t)
  have hagree (z : ℝ) (hz : z ∈ Ioo (-epsilon) epsilon) (x : ℝ) :
      f z x = c (sigma x) (t + z) := by simp only [f, if_pos (hshift_full z hz)]
  have hraw : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun q : ℝ × ℝ => c (sigma q.2) (t + q.1)) (Ioo (-epsilon) epsilon ×ˢ univ) :=
    hjoint.comp (contDiff_snd.prodMk
      (contDiff_const.add contDiff_fst)).contMDiff.contMDiffOn
        (fun q hq => ⟨mem_univ _, hshift q.1 hq.1⟩)
  have hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞ (fun q => f q.1 q.2)
      (Ioo (-epsilon) epsilon ×ˢ univ) :=
    hraw.congr (fun q hq => hagree q.1 hq.1 q.2)
  have hperiodic (z x : ℝ) : f z (x + curvePeriod) = f z x := by
    unfold f
    rw [hshift_sigma]
    split_ifs with hz
    · exact hc.periodic _ hz (sigma x)
    · exact hc.periodic t (Ioo_subset_Icc_self ht) (sigma x)
  refine ⟨epsilon, hepsilon, f, hf, hperiodic, hagree, ?_⟩
  intro x
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  have heq : (fun z => f z x) =ᶠ[𝓝 (0 : ℝ)] fun z => c (sigma x) (t + z) := by
    filter_upwards [isOpen_Ioo.mem_nhds hzero] with z hz
    exact hagree z hz x
  have hvelocity : curveVelocity (fun z => f z x) 0 =
      curveVelocity (fun z => c (sigma x) (t + z)) 0 :=
    congrArg (fun L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) => L 1)
      (heq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n))
  have htime : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun z => c (sigma x) z) t :=
    (hjoint.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds
      (show (x, t) ∈ univ ×ˢ Ioo tau s from ⟨mem_univ _, htt, hts⟩))).comp t
        (contDiffAt_const.prodMk contDiffAt_id).contMDiffAt
  have hchain := M63.curveVelocity_comp
    (gamma := fun z => c (sigma x) z) (phi := fun z => t + z)
    (by simpa only [add_zero] using htime.mdifferentiableAt (by simp))
    ((hasDerivAt_id (0 : ℝ)).const_add t)
  have hchain' : curveVelocity (n := n) (fun z => c (sigma x) (t + z)) 0 =
      curveVelocity (n := n) (fun z => c (sigma x) z) (t + 0) := by
    simpa only [one_smul] using hchain
  have ht0 := congrArg (fun s : ℝ =>
    (curveVelocity (n := n) (fun z => c (sigma x) z) s : EuclideanSpace ℝ (Fin n)))
      (add_zero t)
  exact hvelocity.trans (hchain'.trans (ht0.trans
    (hc.equation t (by simpa only [interior_Icc] using ht) (sigma x))))

end PoincareConjecture
