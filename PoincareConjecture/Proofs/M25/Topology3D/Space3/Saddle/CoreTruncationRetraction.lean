import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PieceData
import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularBandField
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SmoothFlow
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.BoundedHeightTracks
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic











set_option autoImplicit false

open Set Filter Function Metric
open scoped ContDiff Manifold InnerProductSpace NNReal Topology

namespace PoincareConjecture.M25.Topology3D




theorem exists_saddle_core_truncation_retraction
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (sigma z : ℝ) (hsigma : |sigma| = 1)
    (hz : 0 < sigma *
      (z - ⟪(u : E3), psi (D.point, 0)⟫_ℝ))
    (hseams : ∀ i : Fin D.capCount,
      (D.cap i).sign = -sigma →
        0 < sigma *
          ((D.cap i).cutHeight + (D.cap i).sign * (D.cap i).removal - z)) :
    let f : UnitTwoSphere → ℝ :=
      fun q => ⟪(u : E3), psi (q, 0)⟫_ℝ
    let Kz : Set UnitTwoSphere :=
      D.sourceCore ∩ {q | 0 ≤ sigma * (f q - z)}
    let Lz : Set UnitTwoSphere := {q | f q = z}
    ∃ r : UnitTwoSphere → UnitTwoSphere,
      ContMDiff (𝓡 2) (𝓡 2) ∞ r ∧
      Lz ⊆ Kz ∧ Set.MapsTo r Kz Lz ∧ Set.EqOn r id Lz := by
  classical
  let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  let f : UnitTwoSphere → ℝ := fun q => ⟪(u : E3), psi (q, 0)⟫_ℝ
  let c : ℝ := f D.point
  let ell : Fin D.capCount → ℝ := fun i =>
    (D.cap i).cutHeight + (D.cap i).sign * (D.cap i).removal
  let Kz : Set UnitTwoSphere :=
    D.sourceCore ∩ {q | 0 ≤ sigma * (f q - z)}
  let Lz : Set UnitTwoSphere := {q | f q = z}
  change ∃ r : UnitTwoSphere → UnitTwoSphere,
    ContMDiff (𝓡 2) (𝓡 2) ∞ r ∧
    Lz ⊆ Kz ∧ Set.MapsTo r Kz Lz ∧ Set.EqOn r id Lz
  change 0 < sigma * (z - c) at hz
  change ∀ i : Fin D.capCount, (D.cap i).sign = -sigma →
    0 < sigma * (ell i - z) at hseams
  have hj : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ j :=
    collar_central_contMDiff psi hpsi
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f :=
    H.contDiff.contMDiff.comp hj
  have hsigmaCases : sigma = 1 ∨ sigma = -1 := by
    rcases le_total 0 sigma with hs | hs
    · exact Or.inl (by simpa only [abs_of_nonneg hs] using hsigma)
    · exact Or.inr (by rw [abs_of_nonpos hs] at hsigma; linarith)
  have hsigmaSq : sigma * sigma = 1 := by
    rcases hsigmaCases with hs | hs <;> rw [hs] <;> norm_num
  have hsignSq (i : Fin D.capCount) : (D.cap i).sign * (D.cap i).sign = 1 := by
    rcases D.cut_side i with ⟨hi, _⟩ | ⟨hi, _⟩ <;> rw [hi] <;> norm_num
  have hsides (i : Fin D.capCount) :
      ((D.cap i).sign = 1 ∧ ell i < c) ∨
      ((D.cap i).sign = -1 ∧ c < ell i) := by
    have hrem := (D.removal_lt_cutRadius i).trans (D.cutRadius_lt_gap i)
    change (D.cap i).removal < |(D.cap i).cutHeight - c| at hrem
    rcases D.cut_side i with ⟨hi, hm⟩ | ⟨hi, hm⟩
    · change (D.cap i).cutHeight < c at hm
      rw [abs_of_neg (sub_neg.mpr hm)] at hrem
      refine Or.inl ⟨hi, ?_⟩
      dsimp only [ell]
      rw [hi]
      linarith
    · change c < (D.cap i).cutHeight at hm
      rw [abs_of_pos (sub_pos.mpr hm)] at hrem
      refine Or.inr ⟨hi, ?_⟩
      dsimp only [ell]
      rw [hi]
      linarith
  have hcut (i : Fin D.capCount) : 0 < (D.cap i).sign * (z - ell i) := by
    rcases hsigmaCases with hs | hs <;> rcases hsides i with ⟨hi, hside⟩ | ⟨hi, hside⟩
    · have hh := hz
      rw [hs] at hh
      rw [hi]
      linarith
    · have hh := hseams i (by rw [hs]; exact hi)
      rw [hs] at hh
      rw [hi]
      linarith
    · have hh := hseams i (by rw [hs, neg_neg]; exact hi)
      rw [hs] at hh
      rw [hi]
      linarith
    · have hh := hz
      rw [hs] at hh
      rw [hi]
      linarith
  have hplacement (i : Fin D.capCount) (p : UnitTwoSphere)
      (hp : (heightCoordinates (p : E3)).2 ≤ 0) :
      f ((D.cap i).sourceChart p) =
        (D.cap i).cutHeight + (D.cap i).sign *
          ((D.cap i).removal + (D.cap i).scale * ((D.cap i).profile.model p).2) := by
    have htp : (((D.cap i).profile.model p).1,
        (D.cap i).cutHeight + (D.cap i).sign *
          ((D.cap i).removal + (D.cap i).scale * ((D.cap i).profile.model p).2)) ∈
        (D.cap i).tube.source :=
      (D.cap i).tube_source
        ⟨mem_closedBall_zero_iff.mpr ((D.cap i).profile.model_fst_norm_le p), mem_univ _⟩
    dsimp only [f]
    rw [(D.cap i).central_eq p (lt_of_le_of_lt hp (D.cap i).overlap_pos),
      SurgeryCapProfile.capMap_apply]
    exact (D.cap i).tube_height _ htp
  have hcapHeight (i : Fin D.capCount) (q : UnitTwoSphere)
      (hq : q ∈ (D.cap i).sourceCap) :
      (D.cap i).sign * (f q - ell i) ≤ 0 := by
    obtain ⟨p, hp, rfl⟩ := hq
    have hm : ((D.cap i).profile.model p).2 ≤ 0 :=
      (surgeryCapModel_snd_nonpos_iff
        (D.cap i).profile.horizontal (D.cap i).profile.vertical
        (D.cap i).profile.horizontal_smooth (D.cap i).profile.vertical_smooth
        (fun x => ((D.cap i).profile.horizontal_pos x).ne')
        (fun x => ((D.cap i).profile.vertical_pos x).ne')
        (D.cap i).profile.vertical_pos p).mpr hp
    have heq : (D.cap i).sign * (f ((D.cap i).sourceChart p) - ell i) =
        (D.cap i).scale * ((D.cap i).profile.model p).2 := by
      calc
        _ = ((D.cap i).sign * (D.cap i).sign) *
            ((D.cap i).scale * ((D.cap i).profile.model p).2) := by
          rw [hplacement i p hp]
          dsimp only [ell]
          ring
        _ = _ := by rw [hsignSq i, one_mul]
    rw [heq]
    exact mul_nonpos_of_nonneg_of_nonpos (D.cap i).scale_pos.le hm
  have hseamHeight (i : Fin D.capCount) (q : UnitTwoSphere)
      (hq : q ∈ (D.cap i).sourceSeam) : f q = ell i := by
    obtain ⟨p, hp, rfl⟩ := hq
    have hm : ((D.cap i).profile.model p).2 = 0 := by
      have hh := surgeryCapModel_cylinder
        (D.cap i).profile.horizontal (D.cap i).profile.vertical
        (D.cap i).profile.horizontal_smooth (D.cap i).profile.vertical_smooth
        (fun x => ((D.cap i).profile.horizontal_pos x).ne')
        (fun x => ((D.cap i).profile.vertical_pos x).ne')
        (D.cap i).profile.horizontal_near (D.cap i).profile.vertical_far p
        (by rw [hp]; norm_num)
      exact (congrArg Prod.snd hh).trans hp
    rw [hplacement i p hp.le, hm]
    dsimp only [ell]
    ring
  have hlevel : Lz ⊆ Kz := by
    intro q hq
    change f q = z at hq
    have hncap (i : Fin D.capCount) : q ∉ (D.cap i).sourceCap := by
      intro hc
      have hh := hcapHeight i q hc
      rw [hq] at hh
      exact (not_lt_of_ge hh) (hcut i)
    have hcore : q ∈ D.sourceCore := by
      have hh : q ∈ D.sourceCore ∪ ⋃ i, (D.cap i).sourceCap := by
        rw [D.source_cover]
        exact mem_univ _
      rcases hh with hh | hh
      · exact hh
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hh
        exact False.elim (hncap i hi)
    refine ⟨hcore, ?_⟩
    change 0 ≤ sigma * (f q - z)
    simp only [hq, sub_self, mul_zero, le_refl]
  have hincident (q : UnitTwoSphere) (hq : q ∈ Kz) (i : Fin D.capCount)
      (hqi : q ∈ (D.cap i).sourceCap) : (D.cap i).sign = -sigma := by
    have hqs : q ∈ (D.cap i).sourceSeam := by
      rw [← D.source_incidence i]
      exact ⟨hq.1, hqi⟩
    have hheight := hseamHeight i q hqs
    have hbound := hq.2
    change 0 ≤ sigma * (f q - z) at hbound
    have hsep := hcut i
    rw [hheight] at hbound
    rcases hsigmaCases with hs | hs <;> rcases hsides i with ⟨hi, _⟩ | ⟨hi, _⟩
    · rw [hs] at hbound
      rw [hi] at hsep
      exfalso
      linarith
    · simp only [hi, hs]
    · simp only [hi, hs, neg_neg]
    · rw [hs] at hbound
      rw [hi] at hsep
      exfalso
      linarith
  have hKz : IsCompact Kz :=
    D.sourceCore_compact.inter_right
      (isClosed_le continuous_const (continuous_const.mul (hf.continuous.sub continuous_const)))
  have hregular (q : UnitTwoSphere) (hq : q ∈ Kz) :
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f q ≠ 0 := by
    intro hc
    have hqpoint := (D.unique_critical q hq.1).mp hc
    have hh := hq.2
    rw [hqpoint] at hh
    change 0 ≤ sigma * (c - z) at hh
    nlinarith
  obtain ⟨rho, hrho, hrhopsi, hrhonz⟩ := exists_sphere_collar_defining_function psi hpsi
  let U : Set E3 := psi '' (univ ×ˢ Ioo (-1) 1)
  let W : E3 → E3 := fun y => tangentHeightVector (gradient rho y) (u : E3)
  let V : Set E3 := U ∩ W ⁻¹' ({0} : Set E3)ᶜ
  have hU : IsOpen U := collar_image_open psi hpsi
  have hjU (q : UnitTwoSphere) : j q ∈ U :=
    ⟨(q, 0), ⟨mem_univ _, by norm_num⟩, rfl⟩
  have hn (y : E3) (hy : y ∈ U) : gradient rho y ≠ 0 := by
    intro hnzero
    apply hrhonz y hy
    rw [← toDual_gradient, hnzero, map_zero]
  have hW : ContDiffOn ℝ ∞ W U :=
    tangentHeightVector_contDiffOn (gradient rho)
      (contDiffOn_gradient_of_isOpen hU rho hrho) hn (u : E3)
  have hV : IsOpen V :=
    hW.continuousOn.isOpen_inter_preimage hU isClosed_singleton.isOpen_compl
  have hS : IsCompact (j '' Kz) := hKz.image hj.continuous
  have hSV : j '' Kz ⊆ V := by
    rintro y ⟨q, hq, rfl⟩
    refine ⟨hjU q, ?_⟩
    exact tangentHeightVector_ne_zero_of_heightCross _ _
      (collar_regular_height_cross_ne_zero psi hpsi rho hrho hrhopsi hrhonz
        (u : E3) q (hregular q hq))
  obtain ⟨L, hL, hSL, hLV⟩ := exists_compact_between hS hV hSV
  obtain ⟨F, hF, hFc, hFs, hFrho, hFH⟩ :=
    exists_compact_height_band_field hL hU (hLV.trans inter_subset_left)
      rho hrho hn (u : E3) (fun _ => 1) contDiff_const
      (fun y hy _ => (hLV hy).2)
  obtain ⟨Kb, Lb, hKb, hLb⟩ := compactField_bounds F hF hFc
  let Phi : E3 → ℝ → E3 := boundedFlow F hKb hLb
  have hzero (y : E3) (hy : y ∉ U) : F y = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hm => hy (hFs hm))
  have hflowS : ∀ y ∈ range j, ∀ t : ℝ, Phi y t ∈ range j := by
    rintro y ⟨q, rfl⟩ t
    have hflowU := boundedFlow_mapsTo_set F hKb hLb hzero t (hjU q)
    have hfirst := boundedFlow_preserves_firstIntegral F hKb hLb hzero rho
      (fun y hy => (hrho.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))
      (fun y _ => hFrho y) (j q) (hjU q) t
    have hvalue : rho (Phi (j q) t) = 0 :=
      hfirst.trans (hrhopsi (q, 0) ⟨mem_univ _, by norm_num⟩)
    obtain ⟨⟨p, a⟩, hpa, heq⟩ := hflowU
    have ha : a = 0 :=
      (hrhopsi (p, a) hpa).symm.trans ((congrArg rho heq).trans hvalue)
    subst a
    exact ⟨p, heq⟩
  have hunit (y : E3) (hy : y ∈ range j ∩ interior L) : H (F y) = 1 :=
    hFH y (interior_subset hy.2)
  have hPhi : ContDiff ℝ ∞ (fun p : E3 × ℝ => Phi p.1 p.2) :=
    boundedFlow_contDiff F hKb hLb hF hFc
  obtain ⟨e, he, hes, het, hei⟩ := exists_collar_chart psi hpsi
  have hsource0 (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ e.source := by
    rw [hes]
    exact ⟨mem_univ _, by norm_num⟩
  have hej (q : UnitTwoSphere) : e.symm (j q) = (q, 0) := by
    calc
      e.symm (j q) = e.symm (e (q, 0)) :=
        congrArg e.symm (congrFun he (q, 0)).symm
      _ = (q, 0) := e.left_inv (hsource0 q)
  have htarget (t : ℝ) (q : UnitTwoSphere) : Phi (j q) t ∈ e.target := by
    rw [het]
    obtain ⟨p, hp⟩ := hflowS (j q) (mem_range_self q) t
    exact ⟨(p, 0), ⟨mem_univ _, by norm_num⟩, hp⟩
  let P : ℝ × UnitTwoSphere → UnitTwoSphere :=
    fun p => (e.symm (Phi (j p.2) p.1)).1
  have hP : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ P := by
    apply contMDiffOn_univ.mp
    have hi : ContMDiffOn 𝓘(ℝ, E3) (𝓡 2) ∞
        (fun y => (e.symm y).1) e.target :=
      contMDiff_fst.comp_contMDiffOn hei
    have ha : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) ∞
        (fun p : ℝ × UnitTwoSphere => Phi (j p.2) p.1) :=
      hPhi.contMDiff.comp ((hj.comp contMDiff_snd).prodMk_space contMDiff_fst)
    exact hi.comp ha.contMDiffOn (fun p _ => htarget p.1 p.2)
  have hPimage (t : ℝ) (q : UnitTwoSphere) : j (P (t, q)) = Phi (j q) t := by
    obtain ⟨p, hp⟩ := hflowS (j q) (mem_range_self q) t
    change j ((e.symm (Phi (j q) t)).1) = Phi (j q) t
    rw [← hp, hej]
  have hPzero (q : UnitTwoSphere) : P (0, q) = q := by
    change (e.symm (boundedFlow F hKb hLb (j q) 0)).1 = q
    rw [boundedFlow_zero, hej]
  let r : UnitTwoSphere → UnitTwoSphere := fun q => P (z - f q, q)
  have hr : ContMDiff (𝓡 2) (𝓡 2) ∞ r :=
    hP.comp ((contMDiff_const.sub hf).prodMk contMDiff_id)
  refine ⟨r, hr, hlevel, ?_, ?_⟩
  · intro q hq
    let T : ℝ := sigma * (f q - z)
    have hT : 0 ≤ T := hq.2
    let gamma : ℝ → UnitTwoSphere := fun t => P (-sigma * t, q)
    have hg : Continuous gamma :=
      hP.continuous.comp ((continuous_const.mul continuous_id).prodMk continuous_const)
    have hgzero : gamma 0 = q := by
      dsimp only [gamma]
      rw [mul_zero, hPzero]
    have hjg (t : ℝ) : j (gamma t) = Phi (j q) (-sigma * t) :=
      hPimage (-sigma * t) q
    let Good : Set ℝ := {t | gamma t ∈ D.sourceCore ∧ f (gamma t) = f q - sigma * t}
    have hGoodClosed : IsClosed Good :=
      (D.sourceCore_compact.isClosed.preimage hg).inter
        (isClosed_eq (hf.continuous.comp hg)
          (continuous_const.sub (continuous_const.mul continuous_id)))
    have hGoodZero : (0 : ℝ) ∈ Good := by
      change gamma 0 ∈ D.sourceCore ∧ f (gamma 0) = f q - sigma * 0
      rw [hgzero, mul_zero, sub_zero]
      exact ⟨hq.1, rfl⟩
    have hstep (t : ℝ) (ht : t ∈ Good ∩ Ico 0 T) : (Good ∩ Ioc t T).Nonempty := by
      have hgt : gamma t ∈ Kz := by
        refine ⟨ht.1.1, ?_⟩
        change 0 ≤ sigma * (f (gamma t) - z)
        have heq : sigma * (f (gamma t) - z) = T - t := by
          rw [ht.1.2]
          calc
            _ = T - (sigma * sigma) * t := by dsimp only [T]; ring
            _ = _ := by rw [hsigmaSq, one_mul]
        rw [heq]
        exact sub_nonneg.mpr ht.2.2.le
      have hsingle : {j (gamma t)} ⊆ range j ∩ interior L := by
        intro y hy
        rw [mem_singleton_iff.mp hy]
        exact ⟨mem_range_self _, hSL ⟨gamma t, hgt, rfl⟩⟩
      obtain ⟨tau, htau, hlocal⟩ := exists_boundedFlow_unit_height_interval
        F hKb hLb H (S := range j) (A := {j (gamma t)}) (U := interior L)
        isCompact_singleton isOpen_interior hsingle hflowS hunit
      have hheight (s : ℝ) (hs : |s - t| ≤ tau) :
          f (gamma s) = f (gamma t) - sigma * (s - t) := by
        have htime : |-sigma * (s - t)| ≤ tau := by
          simpa only [abs_mul, abs_neg, hsigma, one_mul] using hs
        have heq := (hlocal (j (gamma t)) (mem_singleton _) (-sigma * (s - t)) htime).2
        have hshift : Phi (j (gamma t)) (-sigma * (s - t)) = j (gamma s) := by
          rw [hjg, hjg]
          change boundedFlow F hKb hLb
            (boundedFlow F hKb hLb (j q) (-sigma * t)) (-sigma * (s - t)) =
              boundedFlow F hKb hLb (j q) (-sigma * s)
          rw [← boundedFlow_add]
          congr 1
          ring
        change H (Phi (j (gamma t)) (-sigma * (s - t))) =
          H (j (gamma t)) + -sigma * (s - t) at heq
        rw [hshift] at heq
        change f (gamma s) = f (gamma t) + -sigma * (s - t) at heq
        simpa only [neg_mul, sub_eq_add_neg] using heq
      have havoid : ∀ᶠ s : ℝ in 𝓝 t, ∀ i : Fin D.capCount,
          gamma t ∉ (D.cap i).sourceCap → gamma s ∉ (D.cap i).sourceCap := by
        apply Filter.eventually_all.mpr
        intro i
        by_cases hi : gamma t ∈ (D.cap i).sourceCap
        · exact Filter.Eventually.of_forall (fun _ hh => False.elim (hh hi))
        · have hh := hg.continuousAt.eventually
            ((D.cap i).sourceCap_isCompact.isClosed.isOpen_compl.mem_nhds hi)
          exact hh.mono (fun _ hs _ => hs)
      obtain ⟨eta, heta, hetaball⟩ := Metric.mem_nhds_iff.mp havoid
      let d : ℝ := min (tau / 2) (min (eta / 2) ((T - t) / 2))
      have hd : 0 < d := lt_min (by linarith) (lt_min (by linarith) (by linarith [ht.2.2]))
      have hdtau : d < tau := (min_le_left _ _).trans_lt (by linarith)
      have hdeta : d < eta :=
        ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
      have hdT : d ≤ (T - t) / 2 := (min_le_right _ _).trans (min_le_right _ _)
      let s : ℝ := t + d
      have hst : t < s := by dsimp only [s]; linarith
      have hsT : s ≤ T := by dsimp only [s]; linarith [ht.2.2]
      have hsd : s - t = d := by dsimp only [s]; ring
      have hsabs : |s - t| = d := by rw [hsd, abs_of_pos hd]
      have hh : f (gamma s) = f (gamma t) - sigma * (s - t) :=
        hheight s (by rw [hsabs]; exact hdtau.le)
      have hav (i : Fin D.capCount) :
          gamma t ∉ (D.cap i).sourceCap → gamma s ∉ (D.cap i).sourceCap :=
        hetaball (by rw [Metric.mem_ball, Real.dist_eq, hsabs]; exact hdeta) i
      have hnc (i : Fin D.capCount) : gamma s ∉ (D.cap i).sourceCap := by
        by_cases hi : gamma t ∈ (D.cap i).sourceCap
        · have hsig := hincident (gamma t) hgt i hi
          have hseam : gamma t ∈ (D.cap i).sourceSeam := by
            rw [← D.source_incidence i]
            exact ⟨hgt.1, hi⟩
          have hell := hseamHeight i (gamma t) hseam
          intro hnew
          have hb := hcapHeight i (gamma s) hnew
          rw [hsig] at hb
          have heq : -sigma * (f (gamma s) - ell i) = s - t := by
            rw [hh, hell]
            calc
              _ = (sigma * sigma) * (s - t) := by ring
              _ = _ := by rw [hsigmaSq, one_mul]
          rw [heq] at hb
          exact (not_lt_of_ge hb) (sub_pos.mpr hst)
        · exact hav i hi
      have hcore : gamma s ∈ D.sourceCore := by
        have hcover : gamma s ∈ D.sourceCore ∪ ⋃ i, (D.cap i).sourceCap := by
          rw [D.source_cover]
          exact mem_univ _
        rcases hcover with hc | hc
        · exact hc
        · obtain ⟨i, hi⟩ := mem_iUnion.mp hc
          exact False.elim (hnc i hi)
      refine ⟨s, ⟨hcore, ?_⟩, hst, hsT⟩
      rw [hh, ht.1.2]
      ring
    have hterminal : T ∈ Good :=
      (hGoodClosed.inter isClosed_Icc).mem_of_ge_of_forall_exists_gt hGoodZero hT hstep
    have htime : -sigma * T = z - f q := by
      calc
        _ = -(sigma * sigma) * (f q - z) := by dsimp only [T]; ring
        _ = _ := by rw [hsigmaSq]; ring
    have hendpoint : gamma T = r q := by
      dsimp only [gamma, r]
      rw [htime]
    change f (r q) = z
    rw [← hendpoint, hterminal.2]
    linarith only [htime]
  · intro q hq
    change f q = z at hq
    change P (z - f q, q) = q
    rw [hq, sub_self, hPzero]

end PoincareConjecture.M25.Topology3D
