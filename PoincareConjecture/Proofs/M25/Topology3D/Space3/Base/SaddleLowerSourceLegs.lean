import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.SourceCircleFlowChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.UpperCoreFlow
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.HeightReversalData
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.NativeCapCore
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.Compact










set_option autoImplicit false

open Set Metric Function Filter
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D




theorem exists_saddle_lower_source_legs
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (delta : ℝ) (hdelta : 0 < delta)
    (hsmall : ∀ i : Fin D.capCount,
      delta < D.cutRadius i - (D.cap i).removal)
    (q : Fin 2 → UnitCircle → UnitTwoSphere)
    (hq : ∀ b : Fin 2,
      ContMDiff (𝓡 1) (𝓡 2) ∞ (q b) ∧
      Function.Injective (q b) ∧
      ∀ theta : UnitCircle,
        Function.Injective (mfderiv (𝓡 1) (𝓡 2) (q b) theta))
    (hdisjoint : ∀ b k : Fin 2, b ≠ k →
      Disjoint (range (q b)) (range (q k)))
    (hlevel : (⋃ b : Fin 2, range (q b)) =
      {p : UnitTwoSphere | ⟪(u : E3), psi (p, 0)⟫_ℝ =
        ⟪(u : E3), psi (D.point, 0)⟫_ℝ - delta}) :
    let f : UnitTwoSphere → ℝ := fun p => ⟪(u : E3), psi (p, 0)⟫_ℝ
    let z : ℝ := f D.point - delta
    let ell : Fin D.capCount → ℝ := fun i =>
      (D.cap i).cutHeight + (D.cap i).sign * (D.cap i).removal
    ∃ (label : Fin 2 → Fin D.capCount) (eta : Fin 2 → ℝ)
      (leg : Fin 2 → OpenPartialHomeomorph (UnitCircle × ℝ) UnitTwoSphere),
      Function.Injective label ∧
      (∀ i : Fin D.capCount,
        (D.cap i).sign = 1 ↔ ∃ b : Fin 2, label b = i) ∧
      (∀ i : Fin D.capCount, (D.cap i).sign = 1 → ell i < z) ∧
      (∀ b : Fin 2, 0 < eta b ∧
        (leg b).source = (univ : Set UnitCircle) ×ˢ
          Ioo (ell (label b) - eta b) (z + eta b)) ∧
      (∀ b : Fin 2,
        ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞
          (leg b) (leg b).source) ∧
      (∀ b : Fin 2,
        ContMDiffOn (𝓡 2) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
          (leg b).symm (leg b).target) ∧
      (∀ b : Fin 2, ∀ p : UnitCircle × ℝ,
        p ∈ (leg b).source → f (leg b p) = p.2) ∧
      (∀ b : Fin 2, ∀ theta : UnitCircle,
        leg b (theta, z) = q b theta) ∧
      (∀ b : Fin 2,
        range (fun theta : UnitCircle => leg b (theta, ell (label b))) =
          (D.cap (label b)).sourceSeam) ∧
      (∀ b k : Fin 2, b ≠ k →
        Disjoint
          ((leg b) '' ((univ : Set UnitCircle) ×ˢ Icc (ell (label b)) z))
          ((leg k) '' ((univ : Set UnitCircle) ×ˢ Icc (ell (label k)) z))) ∧
      (⋃ b : Fin 2,
        (leg b) '' ((univ : Set UnitCircle) ×ˢ Icc (ell (label b)) z)) =
          D.sourceCore ∩ {p : UnitTwoSphere | f p ≤ z} := by
  classical
  let f : UnitTwoSphere → ℝ := fun p => ⟪(u : E3), psi (p, 0)⟫_ℝ
  let z : ℝ := f D.point - delta
  let ell : Fin D.capCount → ℝ := fun i =>
    (D.cap i).cutHeight + (D.cap i).sign * (D.cap i).removal
  let Kz : Set UnitTwoSphere := D.sourceCore ∩ {p | f p ≤ z}
  let Lz : Set UnitTwoSphere := {p | f p = z}
  let c : ℝ := f D.point
  have hzc : z < c := by dsimp [z, c]; linarith
  have hfSmooth : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f :=
    (InnerProductSpace.toDual ℝ E3 (u : E3)).contDiff.contMDiff.comp
      (collar_central_contMDiff psi hpsi)
  have hf : Continuous f := hfSmooth.continuous
  have hsides (i : Fin D.capCount) :
      ((D.cap i).sign = 1 ∧ ell i < z) ∨
      ((D.cap i).sign = -1 ∧ z < ell i) := by
    have hgap := D.cutRadius_lt_gap i
    have hsmalli := hsmall i
    change D.cutRadius i < |(D.cap i).cutHeight - c| at hgap
    rcases D.cut_side i with ⟨hi, hm⟩ | ⟨hi, hm⟩
    · change (D.cap i).cutHeight < c at hm
      rw [abs_of_neg (sub_neg.mpr hm)] at hgap
      refine Or.inl ⟨hi, ?_⟩
      dsimp only [ell]
      rw [hi]
      change (D.cap i).cutHeight + 1 * (D.cap i).removal < c - delta
      linarith
    · change c < (D.cap i).cutHeight at hm
      rw [abs_of_pos (sub_pos.mpr hm)] at hgap
      refine Or.inr ⟨hi, ?_⟩
      dsimp only [ell]
      rw [hi]
      change c - delta < (D.cap i).cutHeight + -1 * (D.cap i).removal
      linarith
  have hseams (i : Fin D.capCount) (hi : (D.cap i).sign = 1) : ell i < z := by
    rcases hsides i with ⟨_, hh⟩ | ⟨hs, _⟩
    · exact hh
    · rw [hi] at hs
      norm_num at hs
  have hplacement (i : Fin D.capCount) (p : UnitTwoSphere)
      (hp : (heightCoordinates (p : E3)).2 < (D.cap i).overlapWidth) :
      f ((D.cap i).sourceChart p) =
        (D.cap i).cutHeight + (D.cap i).sign *
          ((D.cap i).removal + (D.cap i).scale * ((D.cap i).profile.model p).2) := by
    have htp : (((D.cap i).profile.model p).1,
        (D.cap i).cutHeight + (D.cap i).sign *
          ((D.cap i).removal + (D.cap i).scale * ((D.cap i).profile.model p).2)) ∈
        (D.cap i).tube.source := (D.cap i).tube_source
      ⟨mem_closedBall_zero_iff.mpr ((D.cap i).profile.model_fst_norm_le p), mem_univ _⟩
    dsimp only [f]
    rw [(D.cap i).central_eq p hp, SurgeryCapProfile.capMap_apply]
    exact (D.cap i).tube_height _ htp
  have hseamHeight (i : Fin D.capCount) (p : UnitTwoSphere)
      (hp : p ∈ (D.cap i).sourceSeam) : f p = ell i := by
    obtain ⟨r, hr, rfl⟩ := hp
    have hm : ((D.cap i).profile.model r).2 = 0 := by
      have hh := surgeryCapModel_cylinder
        (D.cap i).profile.horizontal (D.cap i).profile.vertical
        (D.cap i).profile.horizontal_smooth (D.cap i).profile.vertical_smooth
        (fun x => ((D.cap i).profile.horizontal_pos x).ne')
        (fun x => ((D.cap i).profile.vertical_pos x).ne')
        (D.cap i).profile.horizontal_near (D.cap i).profile.vertical_far r
        (by rw [hr]; norm_num)
      exact (congrArg Prod.snd hh).trans hr
    rw [hplacement i r (by rw [hr]; exact (D.cap i).overlap_pos), hm]
    dsimp only [ell]
    ring
  have hhalf (i : Fin D.capCount) (hi : (D.cap i).sign = 1) :
      ∃ O : Set UnitTwoSphere, IsOpen O ∧ (D.cap i).sourceSeam ⊆ O ∧
        O ∩ {p | f p = ell i} = (D.cap i).sourceSeam ∧
        D.sourceCore ∩ O ⊆ {p | ell i ≤ f p} := by
    let C := D.cap i
    let d := min (C.overlapWidth / 2) (1 / 8)
    have hd : 0 < d := lt_min (half_pos C.overlap_pos) (by norm_num)
    have hdO : d < C.overlapWidth :=
      (min_le_left _ _).trans_lt (by linarith [C.overlap_pos])
    have hdQ : d < 1 / 4 := (min_le_right _ _).trans_lt (by norm_num)
    let V : Set UnitTwoSphere := {p | |(heightCoordinates (p : E3)).2| < d}
    have hVc : Continuous (fun p : UnitTwoSphere => |(heightCoordinates (p : E3)).2|) :=
      ((heightCoordinates.continuous.comp continuous_subtype_val).snd).abs
    have hVo : IsOpen V := isOpen_lt hVc continuous_const
    have hVs : V ⊆ C.sourceChart.source := by
      intro p hp
      exact C.source_band p ((le_abs_self _).trans_lt (hp.trans hdO))
    let O := C.sourceChart '' V
    have hOo : IsOpen O := C.sourceChart.isOpen_image_of_subset_source hVo hVs
    have hSO : C.sourceSeam ⊆ O := by
      rintro p ⟨r, hr, rfl⟩
      refine ⟨r, ?_, rfl⟩
      change |(heightCoordinates (r : E3)).2| < d
      rw [hr, abs_zero]
      exact hd
    have hvheight (p : UnitTwoSphere) (hp : p ∈ V) :
        f (C.sourceChart p) = ell i + C.scale * (heightCoordinates (p : E3)).2 := by
      have hm := surgeryCapModel_cylinder C.profile.horizontal C.profile.vertical
        C.profile.horizontal_smooth C.profile.vertical_smooth
        (fun x => (C.profile.horizontal_pos x).ne')
        (fun x => (C.profile.vertical_pos x).ne') C.profile.horizontal_near
        C.profile.vertical_far p (hp.le.trans hdQ.le)
      have hh := congrArg Prod.snd hm
      change (C.profile.model p).2 = (heightCoordinates (p : E3)).2 at hh
      rw [hplacement i p ((le_abs_self _).trans_lt (hp.trans hdO)), hh]
      dsimp only [ell]
      rw [hi]
      ring
    have hlevelO : O ∩ {p | f p = ell i} = C.sourceSeam := by
      ext p
      constructor
      · rintro ⟨⟨r, hr, rfl⟩, hp⟩
        refine ⟨r, ?_, rfl⟩
        change (heightCoordinates (r : E3)).2 = 0
        have hh := hvheight r hr
        change f (C.sourceChart r) = ell i at hp
        have hz : C.scale * (heightCoordinates (r : E3)).2 = 0 := by linarith
        exact (mul_eq_zero.mp hz).resolve_left C.scale_pos.ne'
      · intro hp
        exact ⟨hSO hp, hseamHeight i p hp⟩
    refine ⟨O, hOo, hSO, hlevelO, ?_⟩
    rintro p ⟨hpK, r, hr, rfl⟩
    change ell i ≤ f (C.sourceChart r)
    by_contra hh
    have hv : (heightCoordinates (r : E3)).2 < 0 := by
      have hh' := hvheight r hr
      apply (mul_lt_mul_iff_right₀ C.scale_pos).mp
      nlinarith
    have hcap : C.sourceChart r ∈ C.sourceCap := ⟨r, hv.le, rfl⟩
    have hs : C.sourceChart r ∈ C.sourceSeam := by
      rw [← D.source_incidence i]
      exact ⟨hpK, hcap⟩
    exact hh (hseamHeight i _ hs).ge
  let fr : UnitTwoSphere → ℝ :=
    fun p => ⟪((-u : UnitTwoSphere) : E3), psi (p, 0)⟫_ℝ
  have hfr (p : UnitTwoSphere) : fr p = -f p := by
    simp only [fr, f, coe_neg_sphere, inner_neg_left]
  have hczr : fr D.reverseHeight.point < -z := by
    change fr D.point < -z
    rw [hfr]
    exact neg_lt_neg hzc
  have hseamsR (i : Fin D.reverseHeight.capCount)
      (hi : (D.reverseHeight.cap i).sign = -1) :
      -z < (D.reverseHeight.cap i).cutHeight +
        (D.reverseHeight.cap i).sign * (D.reverseHeight.cap i).removal := by
    change -(D.cap i).sign = -1 at hi
    have hsign : (D.cap i).sign = 1 := by linarith
    have hh := hseams i hsign
    change -z < -(D.cap i).cutHeight + -(D.cap i).sign * (D.cap i).removal
    dsimp only [ell] at hh
    nlinarith
  obtain ⟨Pm, U, hPm, hU, hKmU, hLmK, hPmzero, hPmadd, hPmderiv, hPmtrack⟩ :=
    exists_saddle_upper_core_flow psi hpsi (-u) D.reverseHeight (-z) hczr hseamsR
  change D.sourceCore ∩ {p | -z ≤ fr p} ⊆ U at hKmU
  change {p | fr p = -z} ⊆ D.sourceCore ∩ {p | -z ≤ fr p} at hLmK
  change ∀ t p, Pm (t, p) ∈ U →
    HasDerivAt (fun s : ℝ => fr (Pm (s, p))) 1 t at hPmderiv
  change ∀ p ∈ D.sourceCore ∩ {p | -z ≤ fr p},
    ∀ t ∈ Icc (0 : ℝ) (fr p - -z),
      Pm (-t, p) ∈ D.sourceCore ∩ {p | -z ≤ fr p} ∧
        fr (Pm (-t, p)) = fr p - t at hPmtrack
  have hKU : Kz ⊆ U := by
    simpa only [Kz, hfr, neg_le_neg_iff] using hKmU
  have hLK : Lz ⊆ Kz := by
    simpa only [Lz, Kz, hfr, neg_inj, neg_le_neg_iff] using hLmK
  let P : ℝ × UnitTwoSphere → UnitTwoSphere := fun p => Pm (-p.1, p.2)
  have hP : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ P :=
    hPm.comp (contMDiff_fst.neg.prodMk contMDiff_snd)
  have hPzero (p : UnitTwoSphere) : P (0, p) = p := by
    simp only [P, neg_zero, hPmzero]
  have hPadd (s t : ℝ) (p : UnitTwoSphere) : P (s, P (t, p)) = P (s + t, p) := by
    change Pm (-s, Pm (-t, p)) = Pm (-(s + t), p)
    rw [hPmadd]
    exact congrArg (fun r => Pm (r, p)) (by ring)
  have hPderiv (t : ℝ) (p : UnitTwoSphere) (hp : P (t, p) ∈ U) :
      HasDerivAt (fun s : ℝ => f (P (s, p))) 1 t := by
    have hh : HasDerivAt (fun s : ℝ => fr (Pm (-s, p))) (-1) t := by
      convert (hPmderiv (-t) p hp).comp t (hasDerivAt_neg t) using 1 <;>
        first | rfl | norm_num
    have hfun : (fun s : ℝ => -fr (Pm (-s, p))) =
        (fun s : ℝ => f (P (s, p))) := by
      funext s
      rw [hfr, neg_neg]
    have hneg : HasDerivAt (fun s : ℝ => -fr (Pm (-s, p))) (1 : ℝ) t := by
      convert hh.neg using 1 <;> first | rfl | norm_num
    rwa [hfun] at hneg
  have htrack (p : UnitTwoSphere) (hp : p ∈ Kz)
      (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (z - f p)) :
      P (t, p) ∈ Kz ∧ f (P (t, p)) = f p + t := by
    have hpm : p ∈ D.sourceCore ∩ {p | -z ≤ fr p} := by
      simpa only [hfr, neg_le_neg_iff] using hp
    have htm : t ∈ Icc (0 : ℝ) (fr p - -z) := by
      rw [hfr]
      constructor <;> linarith [ht.1, ht.2]
    have hh := hPmtrack p hpm t htm
    refine ⟨?_, ?_⟩
    · simpa only [Kz, P, hfr, neg_le_neg_iff] using hh.1
    · have hd := hh.2
      rw [hfr, hfr] at hd
      change f (Pm (-t, p)) = f p + t
      linarith
  have hseamK (i : Fin D.capCount) (hi : (D.cap i).sign = 1) :
      (D.cap i).sourceSeam ⊆ Kz := by
    intro p hp
    have hpcore : p ∈ D.sourceCore := by
      have hh : p ∈ D.sourceCore ∩ (D.cap i).sourceCap := by
        rw [D.source_incidence i]
        exact hp
      exact hh.1
    refine ⟨hpcore, ?_⟩
    change f p ≤ z
    rw [hseamHeight i p hp]
    exact (hseams i hi).le
  have hPc : Continuous P := hP.continuous
  have hPt (t : ℝ) : Continuous (fun p : UnitTwoSphere => P (t, p)) :=
    hPc.comp (continuous_const.prodMk continuous_id)
  have hPneg (p : UnitTwoSphere) : Continuous (fun t : ℝ => P (-t, p)) :=
    hPc.comp (continuous_id.neg.prodMk continuous_const)
  have hheightNeg (p : UnitTwoSphere) (T : ℝ) (hT : 0 ≤ T)
      (hstay : ∀ t ∈ Icc (0 : ℝ) T, P (-t, p) ∈ U) :
      f (P (-T, p)) = f p - T := by
    have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
        HasDerivAt (fun s : ℝ => f (P (-s, p)) + s) 0 t := by
      have hh := ((hPderiv (-t) p (hstay t ht)).comp t
        (hasDerivAt_neg t)).add (hasDerivAt_id t)
      convert hh using 1 <;> first | rfl | norm_num
    have hn : ‖(f (P (-T, p)) + T) - (f (P (0, p)) + 0)‖ ≤ 0 := by
      have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun t ht => (hd t ht).hasDerivWithinAt)
        (fun _ _ => show ‖(0 : ℝ)‖ ≤ 0 by simp) (convex_Icc (0 : ℝ) T)
        (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩)
        (show T ∈ Icc 0 T from ⟨hT, le_rfl⟩)
      simpa only [neg_zero, zero_mul] using hh
    have heq := sub_eq_zero.mp (norm_le_zero_iff.mp hn)
    rw [hPzero, add_zero] at heq
    linarith
  have hdecrease (p : UnitTwoSphere) (hp : p ∈ U)
      (V : Set UnitTwoSphere) (hV : IsOpen V) (hpV : p ∈ V) :
      ∃ t : ℝ, 0 < t ∧ P (-t, p) ∈ V ∧ f (P (-t, p)) = f p - t := by
    have h0 : P (-(0 : ℝ), p) ∈ U ∩ V := by
      rw [neg_zero, hPzero]
      exact ⟨hp, hpV⟩
    have hn := (hPneg p).continuousAt.eventually ((hU.inter hV).mem_nhds h0)
    obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp hn
    have hstay (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (d / 2)) :
        P (-s, p) ∈ U ∩ V := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
      linarith [hs.2]
    exact ⟨d / 2, by positivity, (hstay _ ⟨by positivity, le_rfl⟩).2,
      hheightNeg p (d / 2) (by positivity) (fun s hs => (hstay s hs).1)⟩
  let Ret : UnitTwoSphere → UnitTwoSphere := fun p => P (z - f p, p)
  have hRet : Continuous Ret := hPc.comp ((continuous_const.sub hf).prodMk continuous_id)
  have hRetL (p : UnitTwoSphere) (hp : p ∈ Kz) : Ret p ∈ Lz := by
    have hh := (htrack p hp (z - f p) ⟨sub_nonneg.mpr hp.2, le_rfl⟩).2
    change f (Ret p) = z
    dsimp only [Ret]
    linarith
  have hRetfix (p : UnitTwoSphere) (hp : p ∈ Lz) : Ret p = p := by
    change f p = z at hp
    dsimp only [Ret]
    rw [hp, sub_self, hPzero]
  have hRetmove (p : UnitTwoSphere) (t : ℝ)
      (ht : f (P (t, p)) = f p + t) : Ret (P (t, p)) = Ret p := by
    dsimp only [Ret]
    rw [ht, hPadd]
    exact congrArg (fun r => P (r, p)) (by ring)
  let Q : Fin 2 → Set UnitTwoSphere := fun b => range (q b)
  have hQunion : (⋃ b : Fin 2, Q b) = Lz := hlevel
  have hQL (b : Fin 2) : Q b ⊆ Lz := by
    intro p hp
    rw [← hQunion]
    exact mem_iUnion.mpr ⟨b, hp⟩
  have hQcompact (b : Fin 2) : IsCompact (Q b) :=
    isCompact_range (hq b).1.continuous
  have hQconnected (b : Fin 2) : IsConnected (Q b) := by
    have hdim : 1 < Module.rank ℝ E2 :=
      Module.one_lt_rank_of_one_lt_finrank (by simp [E2])
    let : ConnectedSpace UnitCircle := Subtype.connectedSpace
      (isConnected_sphere hdim (0 : E2) (by norm_num : (0 : ℝ) ≤ 1))
    exact isConnected_range (hq b).1.continuous
  have hQdis (b k : Fin 2) (hbk : b ≠ k) : Disjoint (Q b) (Q k) :=
    hdisjoint b k hbk
  let Kpart : Fin 2 → Set UnitTwoSphere := fun b => Kz ∩ Ret ⁻¹' Q b
  have hKcompact : IsCompact Kz :=
    D.sourceCore_compact.inter_right (isClosed_le hf continuous_const)
  have hKpartCompact (b : Fin 2) : IsCompact (Kpart b) :=
    hKcompact.inter_right ((hQcompact b).isClosed.preimage hRet)
  have hQKpart (b : Fin 2) : Q b ⊆ Kpart b := by
    intro p hp
    refine ⟨hLK (hQL b hp), ?_⟩
    change Ret p ∈ Q b
    rw [hRetfix p (hQL b hp)]
    exact hp
  have hKpartNonempty (b : Fin 2) : (Kpart b).Nonempty :=
    (hQconnected b).nonempty.mono (hQKpart b)
  have hKpartDis (b k : Fin 2) (hbk : b ≠ k) :
      Disjoint (Kpart b) (Kpart k) := by
    apply disjoint_left.mpr
    intro p hp hk
    exact disjoint_left.mp (hQdis b k hbk) hp.2 hk.2
  have hKpartUnion : (⋃ b : Fin 2, Kpart b) = Kz := by
    ext p
    constructor
    · intro hp
      obtain ⟨b, hb⟩ := mem_iUnion.mp hp
      exact hb.1
    · intro hp
      have hr := hRetL p hp
      rw [← hQunion] at hr
      obtain ⟨b, hb⟩ := mem_iUnion.mp hr
      exact mem_iUnion.mpr ⟨b, hp, hb⟩
  let A : Fin D.capCount → Set UnitTwoSphere := fun i =>
    (fun p => P (z - ell i, p)) '' (D.cap i).sourceSeam
  have hAcompact (i : Fin D.capCount) : IsCompact (A i) :=
    (D.cap i).sourceSeam_isCompact.image (hPt (z - ell i))
  have hAconnected (i : Fin D.capCount) : IsConnected (A i) :=
    (D.cap i).sourceSeam_isConnected.image _ (hPt (z - ell i)).continuousOn
  have hAL (i : Fin D.capCount) (hi : (D.cap i).sign = 1) : A i ⊆ Lz := by
    rintro x ⟨p, hp, rfl⟩
    have hh := (htrack p (hseamK i hi hp) (z - ell i)
      ⟨sub_nonneg.mpr (hseams i hi).le, by rw [hseamHeight i p hp]⟩).2
    change f (P (z - ell i, p)) = z
    rw [hseamHeight i p hp] at hh
    linarith
  have hAopen (i : Fin D.capCount) (hi : (D.cap i).sign = 1) :
      ∀ x ∈ A i, ∃ V : Set UnitTwoSphere,
        IsOpen V ∧ x ∈ V ∧ ∀ y ∈ V, y ∈ Lz → y ∈ A i := by
    intro x hx
    obtain ⟨p, hp, hpx⟩ := hx
    obtain ⟨O, hOo, hSO, hOlevel, _hOside⟩ := hhalf i hi
    let T := z - ell i
    have hT : 0 < T := sub_pos.mpr (hseams i hi)
    have hback (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : P (-t, x) ∈ U := by
      have htp : T - t ∈ Icc (0 : ℝ) (z - f p) := by
        rw [hseamHeight i p hp]
        dsimp only [T] at ht ⊢
        constructor <;> linarith [ht.1, ht.2]
      have hh := hKU (htrack p (hseamK i hi hp) (T - t) htp).1
      have heq : P (-t, x) = P (T - t, p) := by
        rw [← hpx, hPadd]
        exact congrArg (fun r => P (r, p)) (by dsimp [T]; ring)
      rw [heq]
      exact hh
    have hEnd : P (-T, x) = p := by
      rw [← hpx, hPadd]
      rw [show -T + (z - ell i) = 0 by dsimp [T]; ring, hPzero]
    have hnegPc : Continuous (fun a : ℝ × UnitTwoSphere => P (-a.1, a.2)) :=
      hPc.comp (continuous_fst.neg.prodMk continuous_snd)
    obtain ⟨J, V, _hJo, hVo, hIJ, hxV, hprod⟩ := generalized_tube_lemma
      (s := Icc (0 : ℝ) T) isCompact_Icc (t := {x}) isCompact_singleton
      (hU.preimage hnegPc) (by
        rintro ⟨t, y⟩ ⟨ht, hy⟩
        change P (-t, y) ∈ U
        change y = x at hy
        rw [hy]
        exact hback t ht)
    let V' := V ∩ (fun y : UnitTwoSphere => P (-T, y)) ⁻¹' O
    refine ⟨V', hVo.inter (hOo.preimage (hPt (-T))), ?_, ?_⟩
    · refine ⟨hxV (mem_singleton x), ?_⟩
      change P (-T, x) ∈ O
      rw [hEnd]
      exact hSO hp
    · intro y hy hyL
      have hstay (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : P (-t, y) ∈ U :=
        hprod (show (t, y) ∈ J ×ˢ V from ⟨hIJ ht, hy.1⟩)
      have hyEnd : P (-T, y) ∈ (D.cap i).sourceSeam := by
        rw [← hOlevel]
        refine ⟨hy.2, ?_⟩
        change f (P (-T, y)) = ell i
        rw [hheightNeg y T hT.le hstay]
        change f y = z at hyL
        rw [hyL]
        dsimp [T]
        ring
      refine ⟨P (-T, y), hyEnd, ?_⟩
      change P (z - ell i, P (-T, y)) = y
      rw [hPadd, show z - ell i + -T = 0 by dsimp [T]; ring, hPzero]
  have hAselect (i : Fin D.capCount) (hi : (D.cap i).sign = 1) :
      ∃ b : Fin 2, A i = Q b := by
    have htwo : A i ⊆ Q 0 ∪ Q 1 := by
      intro x hx
      have hh := hAL i hi hx
      rw [← hQunion] at hh
      obtain ⟨b, hb⟩ := mem_iUnion.mp hh
      fin_cases b
      · exact Or.inl hb
      · exact Or.inr hb
    have hempty : A i ∩ (Q 0 ∩ Q 1) = ∅ := by
      rw [(hQdis 0 1 (by decide)).inter_eq, inter_empty]
    have hsub : ∃ b : Fin 2, A i ⊆ Q b := by
      rcases (isPreconnected_iff_subset_of_disjoint_closed.mp
        (hAconnected i).isPreconnected) (Q 0) (Q 1)
        (hQcompact 0).isClosed (hQcompact 1).isClosed htwo hempty with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    obtain ⟨b, hb⟩ := hsub
    choose V hVo hxV hVsub using hAopen i hi
    let O := ⋃ x : A i, V x.1 x.2
    have hOo : IsOpen O := isOpen_iUnion (fun x : A i => hVo x.1 x.2)
    have hAO : A i ⊆ O := fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxV x hx⟩
    have hOL : O ∩ Lz ⊆ A i := by
      rintro x ⟨hx, hxL⟩
      obtain ⟨y, hy⟩ := mem_iUnion.mp hx
      exact hVsub y.1 y.2 x hy hxL
    refine ⟨b, Subset.antisymm hb ?_⟩
    intro x hxQ
    by_contra hxA
    obtain ⟨a, ha⟩ := (hAconnected i).nonempty
    have hcover : Q b ⊆ O ∪ (A i)ᶜ := by
      intro y _
      by_cases hy : y ∈ A i
      · exact Or.inl (hAO hy)
      · exact Or.inr hy
    obtain ⟨y, hy⟩ := (hQconnected b).isPreconnected O (A i)ᶜ hOo
      (hAcompact i).isClosed.isOpen_compl hcover
      ⟨a, hb ha, hAO ha⟩ ⟨x, hxQ, hxA⟩
    exact hy.2.2 (hOL ⟨hy.2.1, hQL b hy.1⟩)
  have hseamCap (i : Fin D.capCount) : (D.cap i).sourceSeam ⊆ (D.cap i).sourceCap := by
    rintro p ⟨r, hr, rfl⟩
    exact ⟨r, hr.le, rfl⟩
  have hmatching (i k : Fin D.capCount) (hinter : (A i ∩ A k).Nonempty) :
      ∃ p ∈ (D.cap i).sourceSeam, ∃ r ∈ (D.cap k).sourceSeam,
        r = P (ell k - ell i, p) := by
    obtain ⟨x, hxi, hxk⟩ := hinter
    obtain ⟨p, hp, hpx⟩ := hxi
    obtain ⟨r, hr, hrx⟩ := hxk
    refine ⟨p, hp, r, hr, ?_⟩
    calc
      r = P (ell k - z, P (z - ell k, r)) := by
        rw [hPadd, show ell k - z + (z - ell k) = 0 by ring, hPzero]
      _ = P (ell k - z, P (z - ell i, p)) :=
        congrArg (fun y => P (ell k - z, y)) (hrx.trans hpx.symm)
      _ = P (ell k - ell i, p) := by
        rw [hPadd]
        exact congrArg (fun t => P (t, p)) (by ring)
  have hnoLess (i k : Fin D.capCount)
      (hi : (D.cap i).sign = 1) (hk : (D.cap k).sign = 1)
      (hik : ell i < ell k) (hinter : (A i ∩ A k).Nonempty) : False := by
    obtain ⟨p, hp, r, hr, hrp⟩ := hmatching i k hinter
    obtain ⟨O, hOo, hSO, _hOL, hside⟩ := hhalf k hk
    let t0 := ell k - ell i
    have ht0 : 0 < t0 := sub_pos.mpr hik
    have htT : t0 < z - ell i := by dsimp [t0]; linarith [hseams k hk]
    let gamma : ℝ → UnitTwoSphere := fun t => P (t, p)
    have hgc : Continuous gamma := hPc.comp (continuous_id.prodMk continuous_const)
    have hgr : gamma t0 = r := hrp.symm
    have hn : ∀ᶠ t : ℝ in 𝓝 t0, gamma t ∈ O :=
      hgc.continuousAt.eventually (hOo.mem_nhds (hgr.symm ▸ hSO hr))
    obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp hn
    let e := min (d / 2) (t0 / 2)
    have he : 0 < e := lt_min (by positivity) (by positivity)
    have hed : e < d := (min_le_left _ _).trans_lt (by linarith)
    have het : e ≤ t0 / 2 := min_le_right _ _
    have hs : t0 - e ∈ Icc (0 : ℝ) (z - f p) := by
      rw [hseamHeight i p hp]
      constructor <;> linarith
    have hstep := htrack p (hseamK i hi hp) (t0 - e) hs
    have hOstep : gamma (t0 - e) ∈ O := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, show t0 - e - t0 = -e by ring,
        abs_neg, abs_of_pos he]
      exact hed
    have hbound : ell k ≤ f (gamma (t0 - e)) := hside ⟨hstep.1.1, hOstep⟩
    have hh := hstep.2
    rw [hseamHeight i p hp] at hh
    change f (gamma (t0 - e)) = ell i + (t0 - e) at hh
    dsimp only [t0] at hh
    linarith
  have hunique (i k : Fin D.capCount)
      (hi : (D.cap i).sign = 1) (hk : (D.cap k).sign = 1)
      (hinter : (A i ∩ A k).Nonempty) : i = k := by
    rcases lt_trichotomy (ell i) (ell k) with hlt | heq | hgt
    · exact False.elim (hnoLess i k hi hk hlt hinter)
    · by_contra hik
      obtain ⟨p, hp, r, hr, hrp⟩ := hmatching i k hinter
      have hrEq : r = p := by simpa only [heq, sub_self, hPzero] using hrp
      rw [hrEq] at hr
      exact disjoint_left.mp (D.sourceCap_disjoint i k hik)
        (hseamCap i hp) (hseamCap k hr)
    · obtain ⟨x, hxi, hxk⟩ := hinter
      exact False.elim (hnoLess k i hk hi hgt ⟨x, hxk, hxi⟩)
  let Caps : Set UnitTwoSphere := ⋃ i : Fin D.capCount, (D.cap i).sourceCap
  have hCaps : IsCompact Caps :=
    isCompact_iUnion (fun i => (D.cap i).sourceCap_isCompact)
  have houtside : Capsᶜ ⊆ D.sourceCore := by
    intro p hp
    have hh : p ∈ D.sourceCore ∪ ⋃ i : Fin D.capCount, (D.cap i).sourceCap := by
      rw [D.source_cover]
      exact mem_univ _
    rcases hh with hh | hh
    · exact hh
    · exact False.elim (hp hh)
  have hminSeam (b : Fin 2) (p : UnitTwoSphere) (hp : p ∈ Kpart b)
      (hm : IsMinOn f (Kpart b) p) :
      ∃ i : Fin D.capCount, p ∈ (D.cap i).sourceSeam ∧ (D.cap i).sign = 1 := by
    have hpC : p ∈ Caps := by
      by_contra hpC
      obtain ⟨t, ht, hptC, hptH⟩ := hdecrease p (hKU hp.1) Capsᶜ
        hCaps.isClosed.isOpen_compl hpC
      have hptK : P (-t, p) ∈ Kz := by
        refine ⟨houtside hptC, ?_⟩
        change f (P (-t, p)) ≤ z
        rw [hptH]
        exact (sub_le_self _ ht.le).trans hp.1.2
      have hptB : P (-t, p) ∈ Kpart b := by
        refine ⟨hptK, ?_⟩
        change Ret (P (-t, p)) ∈ Q b
        rw [hRetmove p (-t) (by simpa only [sub_eq_add_neg] using hptH)]
        exact hp.2
      have hh : f p ≤ f (P (-t, p)) := hm hptB
      rw [hptH] at hh
      linarith
    obtain ⟨i, hi⟩ := mem_iUnion.mp hpC
    have hps : p ∈ (D.cap i).sourceSeam := by
      rw [← D.source_incidence i]
      exact ⟨hp.1.1, hi⟩
    refine ⟨i, hps, ?_⟩
    have hh := hseamHeight i p hps
    rcases hsides i with ⟨hs, _⟩ | ⟨_, hhigh⟩
    · exact hs
    · have hpz : f p ≤ z := hp.1.2
      linarith
  have hminExists (b : Fin 2) :
      ∃ p ∈ Kpart b, IsMinOn f (Kpart b) p :=
    (hKpartCompact b).exists_isMinOn (hKpartNonempty b) hf.continuousOn
  choose pmin hpmin hmin using hminExists
  choose label hminSeamLabel hlabelLower using
    (fun b => hminSeam b (pmin b) (hpmin b) (hmin b))
  have hAlabel (b : Fin 2) : A (label b) = Q b := by
    obtain ⟨k, hk⟩ := hAselect (label b) (hlabelLower b)
    have hrA : Ret (pmin b) ∈ A (label b) := by
      refine ⟨pmin b, hminSeamLabel b, ?_⟩
      dsimp only [Ret]
      rw [hseamHeight (label b) (pmin b) (hminSeamLabel b)]
    have hrQ : Ret (pmin b) ∈ Q k := by rwa [← hk]
    have hkb : k = b := by
      by_contra hne
      exact disjoint_left.mp (hQdis k b hne) hrQ (hpmin b).2
    simpa only [hkb] using hk
  have hlabelInjective : Injective label := by
    intro b k hbk
    have hQeq : Q b = Q k := by rw [← hAlabel b, ← hAlabel k, hbk]
    obtain ⟨x, hx⟩ := (hQconnected b).nonempty
    by_contra hne
    exact disjoint_left.mp (hQdis b k hne) hx (by rw [← hQeq]; exact hx)
  have hlabelAll (i : Fin D.capCount) :
      (D.cap i).sign = 1 ↔ ∃ b : Fin 2, label b = i := by
    constructor
    · intro hi
      obtain ⟨b, hb⟩ := hAselect i hi
      obtain ⟨x, hx⟩ := (hAconnected i).nonempty
      refine ⟨b, hunique (label b) i (hlabelLower b) hi ⟨x, ?_, hx⟩⟩
      rw [hAlabel b, ← hb]
      exact hx
    · rintro ⟨b, rfl⟩
      exact hlabelLower b
  have hbottomBound (b : Fin 2) (p : UnitTwoSphere) (hp : p ∈ Kpart b) :
      ell (label b) ≤ f p := by
    rw [← hseamHeight (label b) (pmin b) (hminSeamLabel b)]
    exact hmin b hp
  let v : Fin 2 → UnitCircle × ℝ → UnitTwoSphere :=
    fun b p => P (p.2 - z, q b p.1)
  have hstripTrack (b : Fin 2) (theta : UnitCircle) (t : ℝ)
      (ht : t ∈ Icc (ell (label b)) z) :
      v b (theta, t) ∈ Kpart b ∧ f (v b (theta, t)) = t := by
    have hqa : q b theta ∈ A (label b) := by
      rw [hAlabel b]
      exact mem_range_self theta
    obtain ⟨p, hp, hptop⟩ := hqa
    have hveq : v b (theta, t) = P (t - ell (label b), p) := by
      dsimp only [v]
      rw [← hptop, hPadd]
      exact congrArg (fun s => P (s, p)) (by ring)
    have htime : t - ell (label b) ∈ Icc (0 : ℝ) (z - f p) := by
      rw [hseamHeight (label b) p hp]
      constructor <;> linarith [ht.1, ht.2]
    have htr := htrack p (hseamK (label b) (hlabelLower b) hp)
      (t - ell (label b)) htime
    have hh : f (v b (theta, t)) = t := by
      rw [hveq]
      have hh := htr.2
      rw [hseamHeight (label b) p hp] at hh
      linarith
    have hr : Ret (v b (theta, t)) = q b theta := by
      dsimp only [Ret]
      rw [hh]
      dsimp only [v]
      rw [hPadd, show z - t + (t - z) = 0 by ring, hPzero]
    refine ⟨⟨?_, ?_⟩, hh⟩
    · rw [hveq]
      exact htr.1
    · change Ret (v b (theta, t)) ∈ Q b
      rw [hr]
      exact mem_range_self theta
  have hstripImage (b : Fin 2) :
      v b '' (univ ×ˢ Icc (ell (label b)) z) = Kpart b := by
    ext p
    constructor
    · rintro ⟨⟨theta, t⟩, ⟨_, ht⟩, rfl⟩
      exact (hstripTrack b theta t ht).1
    · intro hp
      obtain ⟨theta, htheta⟩ := hp.2
      refine ⟨(theta, f p), ⟨mem_univ _, hbottomBound b p hp, hp.1.2⟩, ?_⟩
      change P (f p - z, q b theta) = p
      rw [htheta]
      dsimp only [Ret]
      rw [hPadd, show f p - z + (z - f p) = 0 by ring, hPzero]
  have hbottomRange (b : Fin 2) :
      range (fun theta : UnitCircle => v b (theta, ell (label b))) =
        (D.cap (label b)).sourceSeam := by
    ext p
    constructor
    · rintro ⟨theta, rfl⟩
      have hqa : q b theta ∈ A (label b) := by
        rw [hAlabel b]
        exact mem_range_self theta
      obtain ⟨r, hr, hrtop⟩ := hqa
      have heq : v b (theta, ell (label b)) = r := by
        dsimp only [v]
        rw [← hrtop, hPadd,
          show ell (label b) - z + (z - ell (label b)) = 0 by ring, hPzero]
      change v b (theta, ell (label b)) ∈ (D.cap (label b)).sourceSeam
      rw [heq]
      exact hr
    · intro hp
      have hrA : Ret p ∈ A (label b) := by
        refine ⟨p, hp, ?_⟩
        dsimp only [Ret]
        rw [hseamHeight (label b) p hp]
      rw [hAlabel b] at hrA
      obtain ⟨theta, htheta⟩ := hrA
      refine ⟨theta, ?_⟩
      change P (ell (label b) - z, q b theta) = p
      rw [htheta]
      dsimp only [Ret]
      rw [hseamHeight (label b) p hp, hPadd,
        show ell (label b) - z + (z - ell (label b)) = 0 by ring, hPzero]
  have htop (b : Fin 2) (theta : UnitCircle) : v b (theta, z) = q b theta := by
    simp only [v, sub_self, hPzero]
  have hclosedU (b : Fin 2) (theta : UnitCircle) (t : ℝ)
      (ht : t ∈ Icc (ell (label b)) z) : v b (theta, t) ∈ U :=
    hKU (hstripTrack b theta t ht).1.1
  have hstripDis (b k : Fin 2) (hbk : b ≠ k) :
      Disjoint (v b '' (univ ×ˢ Icc (ell (label b)) z))
        (v k '' (univ ×ˢ Icc (ell (label k)) z)) := by
    rw [hstripImage b, hstripImage k]
    exact hKpartDis b k hbk
  have hstripUnion :
      (⋃ b : Fin 2, v b '' (univ ×ˢ Icc (ell (label b)) z)) = Kz := by
    calc
      _ = ⋃ b : Fin 2, Kpart b := iUnion_congr hstripImage
      _ = Kz := hKpartUnion
  have hcharts (b : Fin 2) : ∃ eta : ℝ, 0 < eta ∧
      ∃ e : OpenPartialHomeomorph (UnitCircle × ℝ) UnitTwoSphere,
        e.source = (univ : Set UnitCircle) ×ˢ
          Ioo (ell (label b) - eta) (z + eta) ∧
        ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ e e.source ∧
        ContMDiffOn (𝓡 2) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ e.symm e.target ∧
        (∀ p : UnitCircle × ℝ, e p = v b p) ∧
        ∀ p ∈ e.source, f (e p) = p.2 := by
    exact exists_source_circle_flow_chart P hP hPzero hPadd f hfSmooth U hU hPderiv
      (ell (label b)) z (hseams (label b) (hlabelLower b)).le
      (q b) (hq b) (fun theta => hQL b (mem_range_self theta)) (hclosedU b)
  choose eta heta leg hlegSource hlegSmooth hlegInverse hlegMap hlegHeight using hcharts
  have hlegv (b : Fin 2) : (leg b : UnitCircle × ℝ → UnitTwoSphere) = v b :=
    funext (hlegMap b)
  refine ⟨label, eta, leg, hlabelInjective, hlabelAll, hseams,
    fun b => ⟨heta b, hlegSource b⟩, hlegSmooth, hlegInverse,
    hlegHeight, ?_, ?_, ?_, ?_⟩
  · intro b theta
    rw [hlegMap b]
    exact htop b theta
  · intro b
    simpa only [hlegv b] using hbottomRange b
  · intro b k hbk
    simpa only [hlegv b, hlegv k] using hstripDis b k hbk
  · simpa only [hlegv] using hstripUnion

end PoincareConjecture.M25.Topology3D
