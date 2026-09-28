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




theorem exists_saddle_upper_core_flow
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u) (z : ℝ)
    (hcz : ⟪(u : E3), psi (D.point, 0)⟫_ℝ < z)
    (hseams : ∀ i : Fin D.capCount, (D.cap i).sign = -1 →
      z < (D.cap i).cutHeight + (D.cap i).sign * (D.cap i).removal) :
    let f : UnitTwoSphere → ℝ := fun q => ⟪(u : E3), psi (q, 0)⟫_ℝ
    let Kz : Set UnitTwoSphere := D.sourceCore ∩ {q | z ≤ f q}
    let Lz : Set UnitTwoSphere := {q | f q = z}
    ∃ (P : ℝ × UnitTwoSphere → UnitTwoSphere) (U : Set UnitTwoSphere),
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ P ∧
      IsOpen U ∧ Kz ⊆ U ∧ Lz ⊆ Kz ∧
      (∀ q : UnitTwoSphere, P (0, q) = q) ∧
      (∀ s t : ℝ, ∀ q : UnitTwoSphere, P (s, P (t, q)) = P (s + t, q)) ∧
      (∀ t : ℝ, ∀ q : UnitTwoSphere, P (t, q) ∈ U →
        HasDerivAt (fun s : ℝ => f (P (s, q))) 1 t) ∧
      ∀ q ∈ Kz, ∀ t ∈ Icc (0 : ℝ) (f q - z),
        P (-t, q) ∈ Kz ∧ f (P (-t, q)) = f q - t := by
  classical
  let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  let f : UnitTwoSphere → ℝ := fun q => ⟪(u : E3), psi (q, 0)⟫_ℝ
  let c := f D.point
  let ell : Fin D.capCount → ℝ := fun i =>
    (D.cap i).cutHeight + (D.cap i).sign * (D.cap i).removal
  let Kz : Set UnitTwoSphere := D.sourceCore ∩ {q | z ≤ f q}
  let Lz : Set UnitTwoSphere := {q | f q = z}
  change c < z at hcz
  change ∀ i : Fin D.capCount, (D.cap i).sign = -1 → z < ell i at hseams
  have hj : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ j := collar_central_contMDiff psi hpsi
  have hji : Injective j := by
    intro p q hpq
    exact congrArg Prod.fst (hpsi.2.1
      ⟨mem_univ _, by norm_num⟩ ⟨mem_univ _, by norm_num⟩ hpq)
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f := H.contDiff.contMDiff.comp hj
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
    rcases hsides i with ⟨hi, hside⟩ | ⟨hi, _⟩
    · rw [hi]
      linarith
    · have hh := hseams i hi
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
        (D.cap i).tube.source := (D.cap i).tube_source
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
    exact ⟨hcore, hq.ge⟩
  have hincident (q : UnitTwoSphere) (hq : q ∈ Kz) (i : Fin D.capCount)
      (hqi : q ∈ (D.cap i).sourceCap) : (D.cap i).sign = -1 := by
    have hqs : q ∈ (D.cap i).sourceSeam := by
      rw [← D.source_incidence i]
      exact ⟨hq.1, hqi⟩
    have hheight := hseamHeight i q hqs
    rcases hsides i with ⟨_, hi⟩ | ⟨hi, _⟩
    · have hh : z ≤ f q := hq.2
      rw [hheight] at hh
      linarith
    · exact hi
  have hKz : IsCompact Kz :=
    D.sourceCore_compact.inter_right (isClosed_le continuous_const hf.continuous)
  have hregular (q : UnitTwoSphere) (hq : q ∈ Kz) :
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f q ≠ 0 := by
    intro hc
    have hqpoint := (D.unique_critical q hq.1).mp hc
    have hh : z ≤ f q := hq.2
    rw [hqpoint] at hh
    exact (not_le_of_gt hcz) hh
  obtain ⟨rho, hrho, hrhopsi, hrhonz⟩ := exists_sphere_collar_defining_function psi hpsi
  let Vc : Set E3 := psi '' (univ ×ˢ Ioo (-1) 1)
  let W : E3 → E3 := fun y => tangentHeightVector (gradient rho y) (u : E3)
  let Vr : Set E3 := Vc ∩ W ⁻¹' ({0} : Set E3)ᶜ
  have hVc : IsOpen Vc := collar_image_open psi hpsi
  have hjVc (q : UnitTwoSphere) : j q ∈ Vc :=
    ⟨(q, 0), ⟨mem_univ _, by norm_num⟩, rfl⟩
  have hn (y : E3) (hy : y ∈ Vc) : gradient rho y ≠ 0 := by
    intro hnzero
    apply hrhonz y hy
    rw [← toDual_gradient, hnzero, map_zero]
  have hW : ContDiffOn ℝ ∞ W Vc :=
    tangentHeightVector_contDiffOn (gradient rho)
      (contDiffOn_gradient_of_isOpen hVc rho hrho) hn (u : E3)
  have hVr : IsOpen Vr :=
    hW.continuousOn.isOpen_inter_preimage hVc isClosed_singleton.isOpen_compl
  have hS : IsCompact (j '' Kz) := hKz.image hj.continuous
  have hSV : j '' Kz ⊆ Vr := by
    rintro y ⟨q, hq, rfl⟩
    refine ⟨hjVc q, ?_⟩
    exact tangentHeightVector_ne_zero_of_heightCross _ _
      (collar_regular_height_cross_ne_zero psi hpsi rho hrho hrhopsi hrhonz
        (u : E3) q (hregular q hq))
  obtain ⟨L, hL, hSL, hLV⟩ := exists_compact_between hS hVr hSV
  obtain ⟨F, hF, hFc, hFs, hFrho, hFH⟩ :=
    exists_compact_height_band_field hL hVc (hLV.trans inter_subset_left)
      rho hrho hn (u : E3) (fun _ => 1) contDiff_const
      (fun y hy _ => (hLV hy).2)
  obtain ⟨Kb, Lb, hKb, hLb⟩ := compactField_bounds F hF hFc
  let Phi : E3 → ℝ → E3 := boundedFlow F hKb hLb
  have hzero (y : E3) (hy : y ∉ Vc) : F y = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hm => hy (hFs hm))
  have hflowS : ∀ y ∈ range j, ∀ t : ℝ, Phi y t ∈ range j := by
    rintro y ⟨q, rfl⟩ t
    have hflowU := boundedFlow_mapsTo_set F hKb hLb hzero t (hjVc q)
    have hfirst := boundedFlow_preserves_firstIntegral F hKb hLb hzero rho
      (fun y hy => (hrho.contDiffAt (hVc.mem_nhds hy)).differentiableAt (by simp))
      (fun y _ => hFrho y) (j q) (hjVc q) t
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
  let U : Set UnitTwoSphere := j ⁻¹' interior L
  have hU : IsOpen U := isOpen_interior.preimage hj.continuous
  have hKU : Kz ⊆ U := fun q hq => hSL ⟨q, hq, rfl⟩
  have hP : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ P := by
    apply contMDiffOn_univ.mp
    have hi : ContMDiffOn 𝓘(ℝ, E3) (𝓡 2) ∞
        (fun y => (e.symm y).1) e.target := contMDiff_fst.comp_contMDiffOn hei
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
  have hPadd (s t : ℝ) (q : UnitTwoSphere) : P (s, P (t, q)) = P (s + t, q) := by
    apply hji
    rw [hPimage, hPimage, hPimage]
    change boundedFlow F hKb hLb (boundedFlow F hKb hLb (j q) t) s =
      boundedFlow F hKb hLb (j q) (s + t)
    rw [← boundedFlow_add, add_comm t s]
  have hPderiv (t : ℝ) (q : UnitTwoSphere) (hq : P (t, q) ∈ U) :
      HasDerivAt (fun s : ℝ => f (P (s, q))) 1 t := by
    have hfunc : (fun s : ℝ => f (P (s, q))) = (fun s : ℝ => H (Phi (j q) s)) := by
      funext s
      exact congrArg H (hPimage s q)
    have hh : H (F (Phi (j q) t)) = 1 := by
      apply hunit
      refine ⟨hflowS (j q) (mem_range_self q) t, ?_⟩
      rw [← hPimage t q]
      exact hq
    rw [hfunc]
    have hd := H.hasFDerivAt.comp_hasDerivAt t (boundedFlow_hasDerivAt F hKb hLb (j q) t)
    change HasDerivAt (fun s : ℝ => H (Phi (j q) s)) (H (F (Phi (j q) t))) t at hd
    simpa only [hh] using hd
  refine ⟨P, U, hP, hU, hKU, hlevel, hPzero, hPadd, hPderiv, ?_⟩
  intro q hq T hT
  let gamma : ℝ → UnitTwoSphere := fun t => P (-t, q)
  have hg : Continuous gamma :=
    hP.continuous.comp (continuous_id.neg.prodMk continuous_const)
  have hgzero : gamma 0 = q := by dsimp only [gamma]; rw [neg_zero, hPzero]
  have hjg (t : ℝ) : j (gamma t) = Phi (j q) (-t) := hPimage (-t) q
  let Good : Set ℝ := {t | gamma t ∈ D.sourceCore ∧ f (gamma t) = f q - t}
  have hGoodClosed : IsClosed Good :=
    (D.sourceCore_compact.isClosed.preimage hg).inter
      (isClosed_eq (hf.continuous.comp hg) (continuous_const.sub continuous_id))
  have hGoodZero : (0 : ℝ) ∈ Good := by
    change gamma 0 ∈ D.sourceCore ∧ f (gamma 0) = f q - 0
    rw [hgzero, sub_zero]
    exact ⟨hq.1, rfl⟩
  have hstep (t : ℝ) (ht : t ∈ Good ∩ Ico 0 T) : (Good ∩ Ioc t T).Nonempty := by
    have hgt : gamma t ∈ Kz := by
      refine ⟨ht.1.1, ?_⟩
      change z ≤ f (gamma t)
      rw [ht.1.2]
      linarith [hT.2, ht.2.2]
    have hsingle : {j (gamma t)} ⊆ range j ∩ interior L := by
      intro y hy
      rw [mem_singleton_iff.mp hy]
      exact ⟨mem_range_self _, hSL ⟨gamma t, hgt, rfl⟩⟩
    obtain ⟨tau, htau, hlocal⟩ := exists_boundedFlow_unit_height_interval
      F hKb hLb H (S := range j) (A := {j (gamma t)}) (U := interior L)
      isCompact_singleton isOpen_interior hsingle hflowS hunit
    have hheight (s : ℝ) (hs : |s - t| ≤ tau) :
        f (gamma s) = f (gamma t) - (s - t) := by
      have heq := (hlocal (j (gamma t)) (mem_singleton _) (-(s - t))
        (by simpa only [abs_neg] using hs)).2
      have hshift : Phi (j (gamma t)) (-(s - t)) = j (gamma s) := by
        rw [hjg, hjg]
        change boundedFlow F hKb hLb (boundedFlow F hKb hLb (j q) (-t)) (-(s - t)) =
          boundedFlow F hKb hLb (j q) (-s)
        rw [← boundedFlow_add]
        congr 1
        ring
      change H (Phi (j (gamma t)) (-(s - t))) = H (j (gamma t)) + -(s - t) at heq
      rw [hshift] at heq
      change f (gamma s) = f (gamma t) + -(s - t) at heq
      simpa only [sub_eq_add_neg] using heq
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
    have hdeta : d < eta := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
    have hdT : d ≤ (T - t) / 2 := (min_le_right _ _).trans (min_le_right _ _)
    let s : ℝ := t + d
    have hst : t < s := by dsimp only [s]; linarith
    have hsT : s ≤ T := by dsimp only [s]; linarith [ht.2.2]
    have hsd : s - t = d := by dsimp only [s]; ring
    have hsabs : |s - t| = d := by rw [hsd, abs_of_pos hd]
    have hh : f (gamma s) = f (gamma t) - (s - t) :=
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
        have hbound := hcapHeight i (gamma s) hnew
        rw [hsig] at hbound
        nlinarith
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
    (hGoodClosed.inter isClosed_Icc).mem_of_ge_of_forall_exists_gt hGoodZero hT.1 hstep
  refine ⟨⟨hterminal.1, ?_⟩, hterminal.2⟩
  change z ≤ f (gamma T)
  rw [hterminal.2]
  linarith [hT.2]

end PoincareConjecture.M25.Topology3D
