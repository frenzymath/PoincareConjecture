import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.Puncture.Opening









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric TopologicalSpace Filter Classical
open scoped Manifold ContDiff Topology

namespace Poincare

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem ambient_partial_of_diffeomorph
    (U V : Opens E3) (D : Diffeomorph (𝓡 3) (𝓡 3) U V ∞) :
    ∃ e : OpenPartialHomeomorph E3 E3,
      e.source = U ∧ e.target = V ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target ∧
      (∀ x : U, e x = (D x : E3)) ∧
      ∀ y : V, e.symm y = (D.symm y : E3) := by
  let f : E3 → E3 := fun x => if hx : x ∈ U then D ⟨x, hx⟩ else 0
  let g : E3 → E3 := fun y => if hy : y ∈ V then D.symm ⟨y, hy⟩ else 0
  have hf (x : U) : f x = (D x : E3) := dif_pos x.property
  have hg (y : V) : g y = (D.symm y : E3) := dif_pos y.property
  have hfs : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U := by
    intro x hx
    apply ContMDiffAt.contMDiffWithinAt
    apply (contMDiffAt_subtype_iff (x := (⟨x, hx⟩ : U))).mp
    rw [show (fun y : U => f y) = (fun y => (D y : E3)) from funext hf]
    exact (contMDiff_subtype_val.comp D.contMDiff).contMDiffAt
  have hgs : ContMDiffOn (𝓡 3) (𝓡 3) ∞ g V := by
    intro y hy
    apply ContMDiffAt.contMDiffWithinAt
    apply (contMDiffAt_subtype_iff (x := (⟨y, hy⟩ : V))).mp
    rw [show (fun x : V => g x) = (fun x => (D.symm x : E3)) from funext hg]
    exact (contMDiff_subtype_val.comp D.symm.contMDiff).contMDiffAt
  let e : OpenPartialHomeomorph E3 E3 := {
    toFun := f
    invFun := g
    source := U
    target := V
    map_source' := fun x hx => (hf ⟨x, hx⟩).symm ▸ (D ⟨x, hx⟩).property
    map_target' := fun y hy => (hg ⟨y, hy⟩).symm ▸ (D.symm ⟨y, hy⟩).property
    left_inv' := by
      intro x hx
      rw [hf ⟨x, hx⟩, hg (D ⟨x, hx⟩), D.symm_apply_apply]
    right_inv' := by
      intro y hy
      rw [hg ⟨y, hy⟩, hf (D.symm ⟨y, hy⟩), D.apply_symm_apply]
    open_source := U.isOpen
    open_target := V.isOpen
    continuousOn_toFun := hfs.continuousOn
    continuousOn_invFun := hgs.continuousOn }
  exact ⟨e, rfl, rfl, hfs, hgs, hf, hg⟩



theorem exists_puncture_ball_opening_partial {δ : ℝ} (hδ : 0 < δ) :
    ∃ e : OpenPartialHomeomorph E3 E3,
      e.source = ({0} : Set E3)ᶜ ∧ e.target = {x : E3 | 1 < ‖x‖} ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target ∧
      (∀ x : E3, Real.exp δ ≤ ‖x‖ → e x = x) ∧
      (∀ x : E3, Real.exp δ ≤ ‖x‖ → e.symm x = x) ∧
      (∀ {R : ℝ}, Real.exp δ ≤ R → e.IsImage (ball 0 R) (ball 0 R)) ∧
      ∃ F : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ positiveHalfLine ∞,
        StrictMono (fun t => (F t : ℝ)) ∧
        (∀ t, δ ≤ t → (F t : ℝ) = t) ∧
        ∀ (q : Metric.sphere (0 : E3) 1) (t : ℝ),
          e (Real.exp t • (q : E3)) = Real.exp (F t : ℝ) • (q : E3) := by
  obtain ⟨F, D, hmono, hFfix, hradial, hfix⟩ := exists_puncture_ball_opening hδ
  obtain ⟨e, hes, het, he, hei, hD, hDi⟩ :=
    ambient_partial_of_diffeomorph puncturedThreeSpace unitBallExterior D
  have hR : 1 < Real.exp δ := Real.one_lt_exp_iff.mpr hδ
  have hfixed (x : E3) (hx : Real.exp δ ≤ ‖x‖) : e x = x := by
    have hx0 : x ≠ 0 := norm_pos_iff.mp ((Real.exp_pos δ).trans_le hx)
    exact (hD ⟨x, hx0⟩).trans (hfix ⟨x, hx0⟩ hx)
  have hifixed (x : E3) (hx : Real.exp δ ≤ ‖x‖) : e.symm x = x := by
    have hx0 : x ∈ e.source := hes.symm ▸
      (show x ∈ puncturedThreeSpace from norm_pos_iff.mp ((Real.exp_pos δ).trans_le hx))
    calc
      e.symm x = e.symm (e x) := congrArg e.symm (hfixed x hx).symm
      _ = x := e.left_inv hx0
  refine ⟨e, hes, het, he, hei, hfixed, hifixed, ?_, F, hmono, hFfix, ?_⟩
  · intro R hδR x hx
    simp only [mem_ball_zero_iff]
    constructor
    · intro hex
      by_contra hxn
      have hxR := hδR.trans (le_of_not_gt hxn)
      rw [hfixed x hxR] at hex
      exact hxn hex
    · intro hxn
      by_contra hex
      have heR := hδR.trans (le_of_not_gt hex)
      have hxeq : e x = x := (hifixed (e x) heR).symm.trans (e.left_inv hx)
      rw [hxeq] at hex
      exact hex hxn
  · intro q t
    exact (hD (sphereCylinderDiffeomorphPunctured (q, t))).trans (hradial (q, t))

section BallChart

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}

private theorem conjugate_partial
    (b : OpenPartialHomeomorph E3 M) (r : OpenPartialHomeomorph E3 E3)
    (hs : r.source ⊆ b.source) (ht : r.target ⊆ b.source)
    (hb : ContMDiffOn (𝓡 3) I ∞ b b.source)
    (hbi : ContMDiffOn I (𝓡 3) ∞ b.symm b.target)
    (hr : ContMDiffOn (𝓡 3) (𝓡 3) ∞ r r.source)
    (hri : ContMDiffOn (𝓡 3) (𝓡 3) ∞ r.symm r.target) :
    ∃ e : OpenPartialHomeomorph M M,
      e.source = b '' r.source ∧ e.target = b '' r.target ∧
      ContMDiffOn I I ∞ e e.source ∧
      ContMDiffOn I I ∞ e.symm e.target ∧
      (∀ x ∈ r.source, e (b x) = b (r x)) ∧
      ∀ x ∈ r.target, e.symm (b x) = b (r.symm x) := by
  let e := b.symm.trans (r.trans b)
  have hes : e.source = b '' r.source := by
    rw [OpenPartialHomeomorph.trans_source'', OpenPartialHomeomorph.trans_source]
    congr 1
    exact inter_eq_right.mpr (fun x hx => hs hx.1) |>.trans
      (inter_eq_left.mpr (fun x hx => ht (r.map_source hx)))
  have het : e.target = b '' r.target := by
    rw [OpenPartialHomeomorph.trans_target'', OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_target, OpenPartialHomeomorph.coe_trans]
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hbx⟩, rfl⟩
      exact ⟨r x, r.map_source hx.1, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨r.symm x, ⟨⟨r.map_target hx, ht (r.map_source (r.map_target hx))⟩,
        hs (r.map_target hx)⟩, ?_⟩
      simp only [Function.comp_apply, r.right_inv hx]
  have hformula (x : E3) (hx : x ∈ r.source) : e (b x) = b (r x) := by
    simp only [e, OpenPartialHomeomorph.trans_apply, b.left_inv (hs hx)]
  have hiformula (x : E3) (hx : x ∈ r.target) : e.symm (b x) = b (r.symm x) := by
    simp only [e, OpenPartialHomeomorph.coe_trans_symm, Function.comp_apply,
      b.left_inv (ht hx), OpenPartialHomeomorph.symm_symm]
  have he : ContMDiffOn I I ∞ e e.source := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hes ▸ hx
    have hbiy := hbi.contMDiffAt (b.open_target.mem_nhds (b.map_source (hs hy)))
    have hry := hr.contMDiffAt (r.open_source.mem_nhds hy)
    have hbry := hb.contMDiffAt (b.open_source.mem_nhds (ht (r.map_source hy)))
    have hry' : ContMDiffAt (𝓡 3) (𝓡 3) ∞ r (b.symm (b y)) :=
      (b.left_inv (hs hy)).symm ▸ hry
    have hbry' : ContMDiffAt (𝓡 3) I ∞ b (r (b.symm (b y))) :=
      (congrArg r (b.left_inv (hs hy))).symm ▸ hbry
    exact (hbry'.comp (b y) (hry'.comp (b y) hbiy)).contMDiffWithinAt
  have hei : ContMDiffOn I I ∞ e.symm e.target := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := het ▸ hx
    have hbiy := hbi.contMDiffAt (b.open_target.mem_nhds (b.map_source (ht hy)))
    have hriy := hri.contMDiffAt (r.open_target.mem_nhds hy)
    have hbriy := hb.contMDiffAt (b.open_source.mem_nhds (hs (r.map_target hy)))
    have hriy' : ContMDiffAt (𝓡 3) (𝓡 3) ∞ r.symm (b.symm (b y)) :=
      (b.left_inv (ht hy)).symm ▸ hriy
    have hbriy' : ContMDiffAt (𝓡 3) I ∞ b (r.symm (b.symm (b y))) :=
      (congrArg r.symm (b.left_inv (ht hy))).symm ▸ hbriy
    exact (hbriy'.comp (b y) (hriy'.comp (b y) hbiy)).contMDiffWithinAt
  exact ⟨e, hes, het, he, hei, hformula, hiformula⟩



theorem exists_ball_chart_opening
    (b : OpenPartialHomeomorph E3 M)
    (hb : ContMDiffOn (𝓡 3) I ∞ b b.source)
    (hbi : ContMDiffOn I (𝓡 3) ∞ b.symm b.target)
    {δ R : ℝ} (hδ : 0 < δ) (hδR : Real.exp δ < R)
    (hR : closedBall 0 R ⊆ b.source) :
    ∃ e : OpenPartialHomeomorph M M,
      e.source = (b '' ball 0 R) \ {b 0} ∧
      e.target = (b '' ball 0 R) \ (b '' closedBall 0 1) ∧
      ContMDiffOn I I ∞ e e.source ∧
      ContMDiffOn I I ∞ e.symm e.target ∧
      (∀ x ∈ e.source, x ∉ b '' closedBall 0 (Real.exp δ) → e x = x) ∧
      (∀ x ∈ e.target, x ∉ b '' closedBall 0 (Real.exp δ) → e.symm x = x) ∧
      ∃ F : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ positiveHalfLine ∞,
        StrictMono (fun t => (F t : ℝ)) ∧
        (∀ t, δ ≤ t → (F t : ℝ) = t) ∧
        ∀ (q : Metric.sphere (0 : E3) 1) (t : ℝ), Real.exp t < R →
          e (b (Real.exp t • (q : E3))) = b (Real.exp (F t : ℝ) • (q : E3)) := by
  obtain ⟨r, hrs, hrt, hr, hri, hfix, hifix, himage, F, hmono, hFfix, hradial⟩ :=
    exists_puncture_ball_opening_partial hδ
  let q := (himage hδR.le).restr (r.open_source.inter isOpen_ball)
  have hqs : q.source = ({0} : Set E3)ᶜ ∩ ball 0 R := by
    change r.source ∩ ball 0 R = _
    rw [hrs]
  have hqt : q.target = {x : E3 | 1 < ‖x‖} ∩ ball 0 R := by
    change r.target ∩ ball 0 R = _
    rw [hrt]
  have hs : q.source ⊆ b.source := fun x hx => hR (ball_subset_closedBall hx.2)
  have ht : q.target ⊆ b.source := fun x hx => hR (ball_subset_closedBall hx.2)
  obtain ⟨e, hes, het, he, hei, hf, hif⟩ := conjugate_partial b q hs ht hb hbi
    (hr.mono inter_subset_left) (hri.mono inter_subset_left)
  have h1R : 1 < R := (Real.one_lt_exp_iff.mpr hδ).trans hδR
  have h0 : (0 : E3) ∈ b.source := hR (by simp [le_of_lt (zero_lt_one.trans h1R)])
  have hsource : e.source = (b '' ball 0 R) \ {b 0} := by
    rw [hes, hqs]
    ext x
    constructor
    · rintro ⟨y, ⟨hy0, hyR⟩, rfl⟩
      exact ⟨⟨y, hyR, rfl⟩, fun h => hy0
        (b.injOn (hR (ball_subset_closedBall hyR)) h0 h)⟩
    · rintro ⟨⟨y, hyR, rfl⟩, hy0⟩
      exact ⟨y, ⟨fun h => hy0 (congrArg b h), hyR⟩, rfl⟩
  have htarget : e.target = (b '' ball 0 R) \ (b '' closedBall 0 1) := by
    rw [het, hqt]
    ext x
    constructor
    · rintro ⟨y, ⟨hy1, hyR⟩, rfl⟩
      refine ⟨⟨y, hyR, rfl⟩, ?_⟩
      rintro ⟨z, hz, hz'⟩
      have hzy := b.injOn (hR (closedBall_subset_closedBall h1R.le hz))
        (hR (ball_subset_closedBall hyR)) hz'
      exact (not_le_of_gt hy1) (mem_closedBall_zero_iff.mp (hzy ▸ hz))
    · rintro ⟨⟨y, hyR, rfl⟩, hy1⟩
      refine ⟨y, ⟨?_, hyR⟩, rfl⟩
      exact lt_of_not_ge (fun h => hy1 ⟨y, mem_closedBall_zero_iff.mpr h, rfl⟩)
  refine ⟨e, hsource, htarget, he, hei, ?_, ?_, F, hmono, hFfix, ?_⟩
  · intro x hx hxK
    obtain ⟨y, hy, rfl⟩ := hes ▸ hx
    have hyr : Real.exp δ ≤ ‖y‖ := le_of_not_ge
      (fun h => hxK ⟨y, mem_closedBall_zero_iff.mpr h, rfl⟩)
    exact (hf y hy).trans (congrArg b (hfix y hyr))
  · intro x hx hxK
    obtain ⟨y, hy, rfl⟩ := het ▸ hx
    have hyr : Real.exp δ ≤ ‖y‖ := le_of_not_ge
      (fun h => hxK ⟨y, mem_closedBall_zero_iff.mpr h, rfl⟩)
    exact (hif y hy).trans (congrArg b (hifix y hyr))
  · intro y t htR
    have hyq : Real.exp t • (y : E3) ∈ q.source := by
      rw [hqs]
      refine ⟨smul_ne_zero (Real.exp_ne_zero _) (ne_zero_of_mem_unit_sphere y), ?_⟩
      simpa only [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos t), norm_eq_of_mem_sphere y, mul_one] using htR
    exact (hf _ hyq).trans (congrArg b (hradial y t))

end BallChart

end Poincare
