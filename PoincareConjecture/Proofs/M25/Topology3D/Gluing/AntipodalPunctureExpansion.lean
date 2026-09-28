import PoincareConjecture.Proofs.M25.Mathlib.IntervalReparametrization
import PoincareConjecture.Proofs.M25.Mathlib.PositivePolar
import PoincareConjecture.Proofs.M25.Mathlib.CompactBallChart
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.SphereGluing










set_option autoImplicit false

open Set Metric IsManifold
open scoped Manifold ContDiff

namespace PoincareConjecture.M25.Topology3D




theorem exists_antipodal_ball_exterior_chart
    (e : OpenPartialHomeomorph E3 UnitThreeSphere) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hes : e.source = ball 0 R)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (hdis : Disjoint e.target
      ((fun x : UnitThreeSphere => -x) '' e.target)) :
    let q := e 0
    let D := e '' closedBall 0 r
    let m := (r + R) / 2
    let Fix := (e '' ball 0 m ∪
      (fun x : UnitThreeSphere => -x) '' (e '' ball 0 m))ᶜ
    ∃ (rho : OpenPartialHomeomorph ℝ ℝ)
      (H : OpenPartialHomeomorph UnitThreeSphere UnitThreeSphere),
      rho.source = Ioo 0 R ∧ rho.target = Ioo r R ∧
      ContDiffOn ℝ ∞ rho rho.source ∧
      ContDiffOn ℝ ∞ rho.symm rho.target ∧
      StrictMonoOn (rho : ℝ → ℝ) rho.source ∧
      EqOn (rho : ℝ → ℝ) id (Ico m R) ∧
      EqOn (rho.symm : ℝ → ℝ) id (Ico m R) ∧
      H.source = ({q, -q} : Set UnitThreeSphere)ᶜ ∧
      H.target = (D ∪ (fun x : UnitThreeSphere => -x) '' D)ᶜ ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ H H.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ H.symm H.target ∧
      IsConnected H.target ∧
      (∀ x ∈ H.source, H (-x) = -H x) ∧
      (∀ x ∈ H.target, H.symm (-x) = -H.symm x) ∧
      EqOn (H : UnitThreeSphere → UnitThreeSphere) id Fix ∧
      EqOn (H.symm : UnitThreeSphere → UnitThreeSphere) id Fix ∧
      (∀ x : E3, 0 < ‖x‖ → ‖x‖ < R →
        H (e x) = e ((rho ‖x‖ / ‖x‖) • x)) ∧
      (∀ x : E3, r < ‖x‖ → ‖x‖ < R →
        H.symm (e x) = e ((rho.symm ‖x‖ / ‖x‖) • x)) := by
  classical
  let m := (r + R) / 2
  have hrm : r < m := by dsimp [m]; linarith
  have hmR : m < R := by dsimp [m]; linarith
  have hm : 0 < m := hr.trans hrm
  have hR : 0 < R := hr.trans hrR
  obtain ⟨tau, hts, htt, htd, htid, htm, htf, htif⟩ :=
    Real.exists_smooth_interval_reparametrization
      (a := -R) (r := -m) (b := 0) (c := -r)
      (by linarith) (by linarith) (by linarith)
  have hneg0 {s : ℝ} (hs : s ∈ Ioo 0 R) : -s ∈ tau.source := by
    rw [hts]
    exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hnegr {s : ℝ} (hs : s ∈ Ioo r R) : -s ∈ tau.target := by
    rw [htt]
    exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have htmap {s : ℝ} (hs : s ∈ Ioo 0 R) : -tau (-s) ∈ Ioo r R := by
    have hh := htt ▸ tau.map_source (hneg0 hs)
    exact ⟨by linarith [hh.2], by linarith [hh.1]⟩
  have htimap {s : ℝ} (hs : s ∈ Ioo r R) : -tau.symm (-s) ∈ Ioo 0 R := by
    have hh := hts ▸ tau.map_target (hnegr hs)
    exact ⟨by linarith [hh.2], by linarith [hh.1]⟩
  have hrd : ContDiffOn ℝ ∞ (fun s => -tau (-s)) (Ioo 0 R) :=
    (htd.comp contDiff_neg.contDiffOn (fun _ hs => hneg0 hs)).neg
  have hrid : ContDiffOn ℝ ∞ (fun s => -tau.symm (-s)) (Ioo r R) :=
    (htid.comp contDiff_neg.contDiffOn (fun _ hs => hnegr hs)).neg
  let rho : OpenPartialHomeomorph ℝ ℝ :=
    { toFun := fun s => -tau (-s)
      invFun := fun s => -tau.symm (-s)
      source := Ioo 0 R
      target := Ioo r R
      map_source' := fun _ hs => htmap hs
      map_target' := fun _ hs => htimap hs
      left_inv' := fun s hs => by
        rw [neg_neg, tau.left_inv (hneg0 hs), neg_neg]
      right_inv' := fun s hs => by
        rw [neg_neg, tau.right_inv (hnegr hs), neg_neg]
      open_source := isOpen_Ioo
      open_target := isOpen_Ioo
      continuousOn_toFun := hrd.continuousOn
      continuousOn_invFun := hrid.continuousOn }
  have hrmono : StrictMonoOn (rho : ℝ → ℝ) rho.source := by
    intro s hs t ht hst
    exact neg_lt_neg (htm (hneg0 ht) (hneg0 hs) (neg_lt_neg hst))
  have hrfix : EqOn (rho : ℝ → ℝ) id (Ico m R) := by
    intro s hs
    change -tau (-s) = s
    rw [htf ⟨by linarith [hs.2], by linarith [hs.1]⟩, id_eq, neg_neg]
  have hrifix : EqOn (rho.symm : ℝ → ℝ) id (Ico m R) := by
    intro s hs
    change -tau.symm (-s) = s
    rw [htif ⟨by linarith [hs.2], by linarith [hs.1]⟩, id_eq, neg_neg]
  let A0 : Set E3 := {x | 0 < ‖x‖ ∧ ‖x‖ < R}
  let Ar : Set E3 := {x | r < ‖x‖ ∧ ‖x‖ < R}
  let B : E3 → E3 := fun x => (rho ‖x‖ / ‖x‖) • x
  let Bi : E3 → E3 := fun x => (rho.symm ‖x‖ / ‖x‖) • x
  have hBnorm {x : E3} (hx : x ∈ A0) : ‖B x‖ = rho ‖x‖ := by
    have hp := hr.trans (rho.map_source hx).1
    dsimp only [B]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hp hx.1),
      div_mul_cancel₀ _ hx.1.ne']
  have hBinorm {x : E3} (hx : x ∈ Ar) : ‖Bi x‖ = rho.symm ‖x‖ := by
    have hp := (rho.map_target hx).1
    dsimp only [Bi]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hp (hr.trans hx.1)),
      div_mul_cancel₀ _ (hr.trans hx.1).ne']
  have hBmap : MapsTo B A0 Ar := by
    intro x hx
    change r < ‖B x‖ ∧ ‖B x‖ < R
    rw [hBnorm hx]
    exact rho.map_source hx
  have hBimap : MapsTo Bi Ar A0 := by
    intro x hx
    change 0 < ‖Bi x‖ ∧ ‖Bi x‖ < R
    rw [hBinorm hx]
    exact rho.map_target hx
  have hBleft {x : E3} (hx : x ∈ A0) : Bi (B x) = x := by
    change (rho.symm ‖B x‖ / ‖B x‖) • ((rho ‖x‖ / ‖x‖) • x) = x
    rw [hBnorm hx, rho.left_inv hx, smul_smul]
    have hp := hr.trans (rho.map_source hx).1
    rw [div_mul_div_comm, mul_comm ‖x‖, div_self (mul_ne_zero hp.ne' hx.1.ne'), one_smul]
  have hBright {x : E3} (hx : x ∈ Ar) : B (Bi x) = x := by
    change (rho ‖Bi x‖ / ‖Bi x‖) • ((rho.symm ‖x‖ / ‖x‖) • x) = x
    rw [hBinorm hx, rho.right_inv hx, smul_smul]
    have hp := (rho.map_target hx).1
    rw [div_mul_div_comm, mul_comm ‖x‖,
      div_self (mul_ne_zero hp.ne' (hr.trans hx.1).ne'), one_smul]
  have hBd : ContDiffOn ℝ ∞ B A0 := by
    intro x hx
    have hn := contDiffAt_norm (n := ∞) ℝ (norm_pos_iff.mp hx.1)
    have hh := (hrd.contDiffAt (isOpen_Ioo.mem_nhds hx)).comp x hn
    exact ((hh.div hn hx.1.ne').smul contDiffAt_id).contDiffWithinAt
  have hBid : ContDiffOn ℝ ∞ Bi Ar := by
    intro x hx
    have hn := contDiffAt_norm (n := ∞) ℝ (norm_pos_iff.mp (hr.trans hx.1))
    have hh := (hrid.contDiffAt (isOpen_Ioo.mem_nhds hx)).comp x hn
    exact ((hh.div hn (hr.trans hx.1).ne').smul contDiffAt_id).contDiffWithinAt
  let RB : OpenPartialHomeomorph E3 E3 :=
    { toFun := B
      invFun := Bi
      source := A0
      target := Ar
      map_source' := hBmap
      map_target' := hBimap
      left_inv' := fun _ hx => hBleft hx
      right_inv' := fun _ hx => hBright hx
      open_source := (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)
      open_target := (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)
      continuousOn_toFun := hBd.continuousOn
      continuousOn_invFun := hBid.continuousOn }
  let q := e 0
  let D := e '' closedBall 0 r
  let E := e '' ball 0 m
  let K := (e.symm.trans RB).trans e
  have hzero : (0 : E3) ∈ e.source := by rw [hes]; simpa using hR
  have hq : q ∈ e.target := e.map_source hzero
  have hDsub : D ⊆ e.target := e.image_closedBall_subset_target hes hrR
  have hEs : E ⊆ e.target := by
    rintro x ⟨v, hv, rfl⟩
    exact e.map_source (hes.symm ▸ ball_subset_ball hmR.le hv)
  have hnegmem (V : Set UnitThreeSphere) (x : UnitThreeSphere) :
      x ∈ (fun y : UnitThreeSphere => -y) '' V ↔ -x ∈ V := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [neg_neg] using hy
    · intro hx
      exact ⟨-x, hx, neg_neg x⟩
  have hnott {x : UnitThreeSphere} (hx : x ∈ e.target) : -x ∉ e.target := by
    intro hh
    exact disjoint_left.mp hdis hx ((hnegmem e.target x).mpr hh)
  have hnorm {x : UnitThreeSphere} (hx : x ∈ e.target) : ‖e.symm x‖ < R := by
    simpa only [hes, mem_ball_zero_iff] using e.map_target hx
  have hradD {x : UnitThreeSphere} (hx : x ∈ e.target) : x ∉ D ↔ r < ‖e.symm x‖ := by
    constructor
    · intro hd
      exact lt_of_not_ge fun hn => hd ⟨e.symm x,
        mem_closedBall_zero_iff.mpr hn, e.right_inv hx⟩
    · intro hn
      rintro ⟨v, hv, hvx⟩
      have heq : v = e.symm x := e.injOn
        (hes.symm ▸ closedBall_subset_ball hrR hv) (e.map_target hx)
        (hvx.trans (e.right_inv hx).symm)
      exact (not_le_of_gt hn) (heq ▸ mem_closedBall_zero_iff.mp hv)
  have hKsource (x : UnitThreeSphere) : x ∈ K.source ↔ x ∈ e.target ∧ x ≠ q := by
    constructor
    · intro hx
      refine ⟨hx.1.1, ?_⟩
      intro hxq
      have hn : 0 < ‖e.symm x‖ := hx.1.2.1
      rw [hxq, e.left_inv hzero, norm_zero] at hn
      exact lt_irrefl _ hn
    · rintro ⟨hx, hxq⟩
      have hn : 0 < ‖e.symm x‖ := norm_pos_iff.mpr fun h0 =>
        hxq ((e.right_inv hx).symm.trans (congrArg e h0))
      have hz : e.symm x ∈ A0 := ⟨hn, hnorm hx⟩
      exact ⟨⟨hx, hz⟩, hes.symm ▸ mem_ball_zero_iff.mpr (hBmap hz).2⟩
  have hKtarget (x : UnitThreeSphere) : x ∈ K.target ↔ x ∈ e.target ∧ x ∉ D := by
    constructor
    · intro hx
      exact ⟨hx.1, (hradD hx.1).mpr hx.2.1.1⟩
    · rintro ⟨hx, hxd⟩
      have hz : e.symm x ∈ Ar := ⟨(hradD hx).mp hxd, hnorm hx⟩
      refine ⟨hx, hz, ?_⟩
      change Bi (e.symm x) ∈ e.source
      rw [hes]
      exact mem_ball_zero_iff.mpr (hBimap hz).2
  have hKd : ContMDiffOn (𝓡 3) (𝓡 3) ∞ K K.source :=
    he.comp (hBd.contMDiffOn.comp (hei.mono (fun _ hx => hx.1.1))
      (fun _ hx => hx.1.2)) (fun _ hx => hx.2)
  have hKid : ContMDiffOn (𝓡 3) (𝓡 3) ∞ K.symm K.target :=
    he.comp (hBid.contMDiffOn.comp (hei.mono inter_subset_left)
      (fun _ hx => hx.2.1)) (fun _ hx => hx.2.2)
  have hKfix {x : UnitThreeSphere} (hx : x ∈ e.target) (hxe : x ∉ E) :
      K x = x ∧ K.symm x = x := by
    have hn : m ≤ ‖e.symm x‖ := le_of_not_gt fun hh =>
      hxe ⟨e.symm x, mem_ball_zero_iff.mpr hh, e.right_inv hx⟩
    have hp : 0 < ‖e.symm x‖ := hm.trans_le hn
    constructor
    · change e ((rho ‖e.symm x‖ / ‖e.symm x‖) • e.symm x) = x
      rw [hrfix ⟨hn, hnorm hx⟩, id_eq, div_self hp.ne', one_smul, e.right_inv hx]
    · change e ((rho.symm ‖e.symm x‖ / ‖e.symm x‖) • e.symm x) = x
      rw [hrifix ⟨hn, hnorm hx⟩, id_eq, div_self hp.ne', one_smul, e.right_inv hx]
  let Src : Set UnitThreeSphere := ({q, -q} : Set UnitThreeSphere)ᶜ
  let Tgt : Set UnitThreeSphere := (D ∪ (fun x : UnitThreeSphere => -x) '' D)ᶜ
  let Fix : Set UnitThreeSphere := (E ∪ (fun x : UnitThreeSphere => -x) '' E)ᶜ
  let f : UnitThreeSphere → UnitThreeSphere := fun x =>
    if x ∈ e.target then K x else if -x ∈ e.target then -K (-x) else x
  let fi : UnitThreeSphere → UnitThreeSphere := fun x =>
    if x ∈ e.target then K.symm x else if -x ∈ e.target then -K.symm (-x) else x
  have hsrc (x : UnitThreeSphere) : x ∈ Src ↔ x ≠ q ∧ x ≠ -q := by
    simp only [Src, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
  have htgt (x : UnitThreeSphere) : x ∈ Tgt ↔ x ∉ D ∧ -x ∉ D := by
    simp only [Tgt, mem_compl_iff, mem_union, hnegmem, not_or]
  have hfix (x : UnitThreeSphere) : x ∈ Fix ↔ x ∉ E ∧ -x ∉ E := by
    simp only [Fix, mem_compl_iff, mem_union, hnegmem, not_or]
  have hsrcneg {x : UnitThreeSphere} (hx : x ∈ Src) : -x ∈ Src := by
    obtain ⟨hxq, hxn⟩ := (hsrc x).mp hx
    apply (hsrc (-x)).mpr
    constructor
    · intro hh
      exact hxn (by simpa only [neg_neg] using congrArg Neg.neg hh)
    · intro hh
      exact hxq (neg_injective hh)
  have htgtneg {x : UnitThreeSphere} (hx : x ∈ Tgt) : -x ∈ Tgt := by
    simpa only [htgt, neg_neg, and_comm] using (htgt x).mp hx
  have hKtoTgt {x : UnitThreeSphere} (hx : x ∈ K.target) : x ∈ Tgt := by
    obtain ⟨hxt, hxd⟩ := (hKtarget x).mp hx
    exact (htgt x).mpr ⟨hxd, fun hn => hnott hxt (hDsub hn)⟩
  have hKtoSrc {x : UnitThreeSphere} (hx : x ∈ K.source) : x ∈ Src := by
    obtain ⟨hxt, hxq⟩ := (hKsource x).mp hx
    refine (hsrc x).mpr ⟨hxq, ?_⟩
    intro hh
    exact hnott hxt (by simpa only [hh, neg_neg] using hq)
  have hfP {x : UnitThreeSphere} (hx : x ∈ e.target) : f x = K x := if_pos hx
  have hfiP {x : UnitThreeSphere} (hx : x ∈ e.target) : fi x = K.symm x := if_pos hx
  have hfN {x : UnitThreeSphere} (hx : -x ∈ e.target) : f x = -K (-x) := by
    have hn : x ∉ e.target := by simpa only [neg_neg] using hnott hx
    simp only [f, if_neg hn, if_pos hx]
  have hfiN {x : UnitThreeSphere} (hx : -x ∈ e.target) : fi x = -K.symm (-x) := by
    have hn : x ∉ e.target := by simpa only [neg_neg] using hnott hx
    simp only [fi, if_neg hn, if_pos hx]
  have hfodd (x : UnitThreeSphere) : f (-x) = -f x := by
    by_cases hx : x ∈ e.target
    · rw [hfP hx, hfN (by simpa only [neg_neg] using hx), neg_neg]
    · by_cases hn : -x ∈ e.target
      · rw [hfN hn, hfP hn, neg_neg]
      · simp only [f, if_neg hx, if_neg hn, neg_neg]
  have hfiodd (x : UnitThreeSphere) : fi (-x) = -fi x := by
    by_cases hx : x ∈ e.target
    · rw [hfiP hx, hfiN (by simpa only [neg_neg] using hx), neg_neg]
    · by_cases hn : -x ∈ e.target
      · rw [hfiN hn, hfiP hn, neg_neg]
      · simp only [fi, if_neg hx, if_neg hn, neg_neg]
  have hfmap : MapsTo f Src Tgt := by
    intro x hx
    by_cases ht : x ∈ e.target
    · rw [hfP ht]
      exact hKtoTgt (K.map_source ((hKsource x).mpr ⟨ht, ((hsrc x).mp hx).1⟩))
    · by_cases hn : -x ∈ e.target
      · rw [hfN hn]
        exact htgtneg (hKtoTgt (K.map_source
          ((hKsource (-x)).mpr ⟨hn, ((hsrc (-x)).mp (hsrcneg hx)).1⟩)))
      · simp only [f, if_neg ht, if_neg hn]
        exact (htgt x).mpr ⟨fun hd => ht (hDsub hd), fun hd => hn (hDsub hd)⟩
  have hfimap : MapsTo fi Tgt Src := by
    intro x hx
    by_cases ht : x ∈ e.target
    · rw [hfiP ht]
      exact hKtoSrc (K.map_target ((hKtarget x).mpr ⟨ht, ((htgt x).mp hx).1⟩))
    · by_cases hn : -x ∈ e.target
      · rw [hfiN hn]
        exact hsrcneg (hKtoSrc (K.map_target
          ((hKtarget (-x)).mpr ⟨hn, ((htgt x).mp hx).2⟩)))
      · simp only [fi, if_neg ht, if_neg hn]
        refine (hsrc x).mpr ⟨fun hh => ht (hh.symm ▸ hq), ?_⟩
        intro hh
        exact hn (by simpa only [hh, neg_neg] using hq)
  have hfleft {x : UnitThreeSphere} (hx : x ∈ Src) : fi (f x) = x := by
    by_cases ht : x ∈ e.target
    · have hk := (hKsource x).mpr ⟨ht, ((hsrc x).mp hx).1⟩
      rw [hfP ht, hfiP ((hKtarget _).mp (K.map_source hk)).1, K.left_inv hk]
    · by_cases hn : -x ∈ e.target
      · have hk := (hKsource (-x)).mpr ⟨hn, ((hsrc (-x)).mp (hsrcneg hx)).1⟩
        rw [hfN hn, hfiodd, hfiP ((hKtarget _).mp (K.map_source hk)).1,
          K.left_inv hk, neg_neg]
      · simp only [f, fi, if_neg ht, if_neg hn]
  have hfright {x : UnitThreeSphere} (hx : x ∈ Tgt) : f (fi x) = x := by
    by_cases ht : x ∈ e.target
    · have hk := (hKtarget x).mpr ⟨ht, ((htgt x).mp hx).1⟩
      rw [hfiP ht, hfP ((hKsource _).mp (K.map_target hk)).1, K.right_inv hk]
    · by_cases hn : -x ∈ e.target
      · have hk := (hKtarget (-x)).mpr ⟨hn, ((htgt x).mp hx).2⟩
        rw [hfiN hn, hfodd, hfP ((hKsource _).mp (K.map_target hk)).1,
          K.right_inv hk, neg_neg]
      · simp only [f, fi, if_neg ht, if_neg hn]
  have hffix : EqOn f id Fix := by
    intro x hx
    obtain ⟨hxE, hnxE⟩ := (hfix x).mp hx
    by_cases ht : x ∈ e.target
    · exact (hfP ht).trans (hKfix ht hxE).1
    · by_cases hn : -x ∈ e.target
      · rw [hfN hn, (hKfix hn hnxE).1, neg_neg]
        rfl
      · exact by simp only [f, if_neg ht, if_neg hn, id_eq]
  have hfifix : EqOn fi id Fix := by
    intro x hx
    obtain ⟨hxE, hnxE⟩ := (hfix x).mp hx
    by_cases ht : x ∈ e.target
    · exact (hfiP ht).trans (hKfix ht hxE).2
    · by_cases hn : -x ∈ e.target
      · rw [hfiN hn, (hKfix hn hnxE).2, neg_neg]
        rfl
      · exact by simp only [fi, if_neg ht, if_neg hn, id_eq]
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
  have hneg : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : UnitThreeSphere => -x) :=
    contMDiff_neg_sphere
  let Mid := e '' closedBall 0 m
  let Outside := (Mid ∪ (fun x : UnitThreeSphere => -x) '' Mid)ᶜ
  have hMid : IsCompact Mid := e.isCompact_image_closedBall hes hmR
  have hOutside : IsOpen Outside :=
    (hMid.union (hMid.image hneg.continuous)).isClosed.isOpen_compl
  have hOutFix : Outside ⊆ Fix := by
    intro x hx hh
    apply hx
    rcases hh with hh | hh
    · exact Or.inl (image_mono ball_subset_closedBall hh)
    · exact Or.inr (image_mono (image_mono ball_subset_closedBall) hh)
  have hOutsideMem {x : UnitThreeSphere} (hx : x ∉ e.target) (hn : -x ∉ e.target) :
      x ∈ Outside := by
    rintro (hy | hy)
    · exact hx (e.image_closedBall_subset_target hes hmR hy)
    · exact hn (e.image_closedBall_subset_target hes hmR ((hnegmem Mid x).mp hy))
  have hfd : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f Src := by
    intro x hx
    by_cases ht : x ∈ e.target
    · have hk := (hKsource x).mpr ⟨ht, ((hsrc x).mp hx).1⟩
      exact (((hKd x hk).contMDiffAt (K.open_source.mem_nhds hk)).congr_of_eventuallyEq
        (Filter.eventuallyEq_of_mem (e.open_target.mem_nhds ht)
          (fun y hy => hfP hy))).contMDiffWithinAt
    · by_cases hn : -x ∈ e.target
      · have hk := (hKsource (-x)).mpr ⟨hn, ((hsrc (-x)).mp (hsrcneg hx)).1⟩
        have hh := (hneg (K (-x))).comp x
          (((hKd (-x) hk).contMDiffAt (K.open_source.mem_nhds hk)).comp x (hneg x))
        exact (hh.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem
          ((e.open_target.preimage hneg.continuous).mem_nhds hn)
          (fun y hy => hfN hy))).contMDiffWithinAt
      · exact ((contMDiff_id x).congr_of_eventuallyEq (Filter.eventuallyEq_of_mem
          (hOutside.mem_nhds (hOutsideMem ht hn))
          (fun y hy => hffix (hOutFix hy)))).contMDiffWithinAt
  have hfid : ContMDiffOn (𝓡 3) (𝓡 3) ∞ fi Tgt := by
    intro x hx
    by_cases ht : x ∈ e.target
    · have hk := (hKtarget x).mpr ⟨ht, ((htgt x).mp hx).1⟩
      exact (((hKid x hk).contMDiffAt (K.open_target.mem_nhds hk)).congr_of_eventuallyEq
        (Filter.eventuallyEq_of_mem (e.open_target.mem_nhds ht)
          (fun y hy => hfiP hy))).contMDiffWithinAt
    · by_cases hn : -x ∈ e.target
      · have hk := (hKtarget (-x)).mpr ⟨hn, ((htgt x).mp hx).2⟩
        have hh := (hneg (K.symm (-x))).comp x
          (((hKid (-x) hk).contMDiffAt (K.open_target.mem_nhds hk)).comp x (hneg x))
        exact (hh.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem
          ((e.open_target.preimage hneg.continuous).mem_nhds hn)
          (fun y hy => hfiN hy))).contMDiffWithinAt
      · exact ((contMDiff_id x).congr_of_eventuallyEq (Filter.eventuallyEq_of_mem
          (hOutside.mem_nhds (hOutsideMem ht hn))
          (fun y hy => hfifix (hOutFix hy)))).contMDiffWithinAt
  have hDcompact : IsCompact D := e.isCompact_image_closedBall hes hrR
  let H : OpenPartialHomeomorph UnitThreeSphere UnitThreeSphere :=
    { toFun := f
      invFun := fi
      source := Src
      target := Tgt
      map_source' := hfmap
      map_target' := hfimap
      left_inv' := fun _ hx => hfleft hx
      right_inv' := fun _ hx => hfright hx
      open_source := ((finite_singleton (-q)).insert q).isClosed.isOpen_compl
      open_target := (hDcompact.union (hDcompact.image hneg.continuous)).isClosed.isOpen_compl
      continuousOn_toFun := hfd.continuousOn
      continuousOn_invFun := hfid.continuousOn }
  let theta := threeSphereStereographic q
  have hthetaImage : theta.symm '' ({0} : Set E3)ᶜ = Src := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzt : z ∈ theta.target := by rw [threeSphereStereographic_target]; trivial
      refine (hsrc _).mpr ⟨?_, ?_⟩
      · simpa only [theta, threeSphereStereographic_source, mem_compl_iff, mem_singleton_iff]
          using theta.map_target hzt
      · intro hh
        have heq := congrArg theta hh
        rw [theta.right_inv hzt, threeSphereStereographic_apply_antipode] at heq
        exact hz heq
    · intro hx
      obtain ⟨hxq, hxn⟩ := (hsrc x).mp hx
      have hxs : x ∈ theta.source := by
        simpa only [theta, threeSphereStereographic_source, mem_compl_iff, mem_singleton_iff]
          using hxq
      refine ⟨theta x, ?_, theta.left_inv hxs⟩
      intro hh
      have hh' := congrArg theta.symm hh
      rw [theta.left_inv hxs, threeSphereStereographic_symm_zero] at hh'
      exact hxn hh'
  have hSrc : IsConnected Src := by
    rw [← hthetaImage]
    exact (isConnected_compl_singleton_of_one_lt_rank
      (by rw [← Module.finrank_eq_rank]; norm_num) (0 : E3)).image theta.symm
      (theta.symm.continuousOn.mono (by
        rw [OpenPartialHomeomorph.symm_source, threeSphereStereographic_target]
        exact subset_univ _))
  have hTgt : IsConnected H.target := by
    rw [← H.image_source_eq_target]
    exact hSrc.image H H.continuousOn
  refine ⟨rho, H, rfl, rfl, hrd, hrid, hrmono, hrfix, hrifix, rfl, rfl,
    hfd, hfid, hTgt, fun x _ => hfodd x, fun x _ => hfiodd x, hffix, hfifix, ?_, ?_⟩
  · intro x _ hxR
    have hx : x ∈ e.source := hes.symm ▸ mem_ball_zero_iff.mpr hxR
    change f (e x) = e (B x)
    rw [hfP (e.map_source hx)]
    change e (B (e.symm (e x))) = e (B x)
    rw [e.left_inv hx]
  · intro x _ hxR
    have hx : x ∈ e.source := hes.symm ▸ mem_ball_zero_iff.mpr hxR
    change fi (e x) = e (Bi x)
    rw [hfiP (e.map_source hx)]
    change e (Bi (e.symm (e x))) = e (Bi x)
    rw [e.left_inv hx]

end PoincareConjecture.M25.Topology3D
