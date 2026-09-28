import PoincareConjecture.Proofs.M76.Mathlib.ContractibleBallExtension
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric unitInterval NormedSpace

namespace PoincareConjecture.M76.HamiltonIndexOne

variable {V2 : Type*} [NormedAddCommGroup V2] [NormedSpace ℝ V2]
local notation "J" => Icc (-1 : ℝ) 1
local notation "Q" => sphere (0 : V2) 1

theorem glue_closed_cover
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (s t : Set X) (hs : IsClosed s) (ht : IsClosed t) (hcover : s ∪ t = univ)
    (f : C(s, Y)) (g : C(t, Y))
    (hagree : ∀ (x : X) (hxs : x ∈ s) (hxt : x ∈ t),
      f ⟨x, hxs⟩ = g ⟨x, hxt⟩) :
    ∃ h : C(X, Y), (∀ x : s, h x = f x) ∧ ∀ x : t, h x = g x := by
  classical
  have hmem (x : X) : x ∈ s ∨ x ∈ t := by
    have hx : x ∈ s ∪ t := hcover.symm ▸ mem_univ x
    exact hx
  let h : X → Y := fun x => if hx : x ∈ s then f ⟨x, hx⟩ else
    g ⟨x, (hmem x).resolve_left hx⟩
  have hleft (x : s) : h x = f x := by simp only [h, dif_pos x.property]
  have hright (x : t) : h x = g x := by
    by_cases hx : (x : X) ∈ s
    · simp only [h, dif_pos hx]
      exact hagree x hx x.property
    · simp only [h, dif_neg hx]
  have hcs : ContinuousOn h s := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact f.continuous.congr (fun x => (hleft x).symm)
  have hct : ContinuousOn h t := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact g.continuous.congr (fun x => (hright x).symm)
  have hc := hcs.union_of_isClosed hct hs ht
  rw [hcover, continuousOn_univ] at hc
  exact ⟨⟨h, hc⟩, hleft, hright⟩

omit [NormedSpace ℝ V2] in
private theorem marked_annulus_homotopy
    (rho : C(J × Q, Q))
    (hminus : ∀ u : Q, rho (⟨-1, by norm_num⟩, u) = u) :
    Nonempty ((ContinuousMap.id (J × Q)).Homotopy
      (⟨fun z => (⟨0, by norm_num⟩, rho z),
        continuous_const.prodMk rho.continuous⟩ : C(J × Q, J × Q))) := by
  let z0 : J := ⟨0, by norm_num⟩
  let middle : C(J × Q, J × Q) :=
    ⟨fun z => (z0, z.2), continuous_const.prodMk continuous_snd⟩
  let last : C(J × Q, J × Q) :=
    ⟨fun z => (z0, rho z), continuous_const.prodMk rho.continuous⟩
  have hfirst (a : I) (s : J) : (1 - (a : ℝ)) * (s : ℝ) ∈ J := by
    rcases a.property with ⟨ha0, ha1⟩
    rcases s.property with ⟨hs0, hs1⟩
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr ha1)
        (show 0 ≤ (s : ℝ) + 1 by linarith)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hs1)]
  let H1 : (ContinuousMap.id (J × Q)).Homotopy middle :=
    { toFun := fun p => (⟨(1 - (p.1 : ℝ)) * (p.2.1 : ℝ),
        hfirst p.1 p.2.1⟩, p.2.2)
      continuous_toFun :=
        (((continuous_const.sub continuous_fst.subtype_val).mul
          continuous_snd.fst.subtype_val).subtype_mk _).prodMk continuous_snd.snd
      map_zero_left := by intro z; ext <;> simp
      map_one_left := by intro z; ext <;> simp [middle, z0] }
  have hsecond (a : I) (s : J) : -1 + (a : ℝ) * ((s : ℝ) + 1) ∈ J := by
    rcases a.property with ⟨ha0, ha1⟩
    rcases s.property with ⟨hs0, hs1⟩
    have hs : 0 ≤ (s : ℝ) + 1 := by linarith
    constructor
    · nlinarith [mul_nonneg ha0 hs]
    · nlinarith [mul_nonneg (sub_nonneg.mpr ha1) hs]
  let shift : C(I × (J × Q), J × Q) :=
    ⟨fun p => (⟨-1 + (p.1 : ℝ) * ((p.2.1 : ℝ) + 1),
        hsecond p.1 p.2.1⟩, p.2.2),
      (((continuous_const.add (continuous_fst.subtype_val.mul
        (continuous_snd.fst.subtype_val.add continuous_const))).subtype_mk _).prodMk
          continuous_snd.snd)⟩
  let H2 : middle.Homotopy last :=
    { toFun := fun p => (z0, rho (shift p))
      continuous_toFun := continuous_const.prodMk (rho.continuous.comp shift.continuous)
      map_zero_left := by
        intro z
        change (z0, rho (shift (0, z))) = (z0, z.2)
        apply congrArg (Prod.mk z0)
        change rho (⟨-1 + (0 : ℝ) * ((z.1 : ℝ) + 1), _⟩, z.2) = z.2
        simpa only [zero_mul, add_zero] using hminus z.2
      map_one_left := by
        intro z
        change (z0, rho (shift (1, z))) = (z0, rho z)
        apply congrArg (Prod.mk z0)
        congr 1
        apply Prod.ext
        · apply Subtype.ext
          change -1 + (1 : ℝ) * ((z.1 : ℝ) + 1) = (z.1 : ℝ)
          ring
        · rfl }
  exact ⟨H1.trans H2⟩

theorem exists_marked_product_complement_retraction
    [FiniteDimensional ℝ V2]
    {R : ℝ} (hR : 0 < R)
    (K V : Set (J × closedBall (0 : V2) R)) (hK : IsCompact K)
    (hVK : V ⊆ K) (hKr : ∀ x ∈ K, ‖(x.2 : V2)‖ < R)
    (rho : C(↥(Vᶜ : Set (J × closedBall (0 : V2) R)), Q))
    (hminus : ∀ (u : Q) (x : ↥(Vᶜ : Set (J × closedBall (0 : V2) R))),
      ((x : J × closedBall (0 : V2) R).1 : ℝ) = -1 →
      ((x : J × closedBall (0 : V2) R).2 : V2) = R • (u : V2) → rho x = u) :
    ∃ r : C(↥(Vᶜ : Set (J × closedBall (0 : V2) R)), J × Q),
      ∀ (s : J) (u : Q) (x : ↥(Vᶜ : Set (J × closedBall (0 : V2) R))),
        (x : J × closedBall (0 : V2) R).1 = s →
        ((x : J × closedBall (0 : V2) R).2 : V2) = R • (u : V2) →
          r x = (s, u) := by
  classical
  let M := J × closedBall (0 : V2) R
  let D : Set M := Vᶜ
  let radial : C(M, ℝ) :=
    ⟨fun x => ‖(x.2 : V2)‖, continuous_norm.comp (continuous_subtype_val.comp continuous_snd)⟩
  obtain ⟨b, hb, hbR, hKb⟩ : ∃ b : ℝ, 0 < b ∧ b < R ∧
      ∀ x ∈ K, radial x < b := by
    rcases K.eq_empty_or_nonempty with hKe | hKn
    · refine ⟨R / 2, by linarith, by linarith, ?_⟩
      intro x hx
      exact (hKe ▸ hx).elim
    · obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hKn radial.continuous.continuousOn
      obtain ⟨b, hxb, hbR⟩ := exists_between (hKr x hx)
      exact ⟨b, lt_of_le_of_lt (norm_nonneg _) hxb, hbR,
        fun y hy => lt_of_le_of_lt (hmax hy) hxb⟩
  have hnorm (u : Q) : ‖(u : V2)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
  have hRu (u : Q) : ‖R • (u : V2)‖ = R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR, hnorm, mul_one]
  have hinc (z : J × Q) :
      (z.1, ⟨R • (z.2 : V2), mem_closedBall_zero_iff.mpr (hRu z.2).le⟩) ∉ V := by
    intro hv
    have hk := hKb (z.1, ⟨R • (z.2 : V2),
      mem_closedBall_zero_iff.mpr (hRu z.2).le⟩) (hVK hv)
    change ‖R • (z.2 : V2)‖ < b at hk
    rw [hRu] at hk
    exact (not_lt_of_ge hbR.le) hk
  let inc : C(J × Q, D) :=
    ⟨fun z => ⟨(z.1, ⟨R • (z.2 : V2), mem_closedBall_zero_iff.mpr (hRu z.2).le⟩),
      hinc z⟩,
      by fun_prop⟩
  have hlow (u : Q) : (rho.comp inc) (⟨-1, by norm_num⟩, u) = u :=
    hminus u _ rfl rfl
  obtain ⟨H⟩ := marked_annulus_homotopy (rho.comp inc) hlow
  let z0 : J := ⟨0, by norm_num⟩
  let radius : C(D, ℝ) := radial.comp ⟨Subtype.val, continuous_subtype_val⟩
  let W : Set D := {x | b ≤ radius x}
  let low : Set D := {x | radius x ≤ b}
  let rw : C(W, ℝ) := radius.comp ⟨Subtype.val, continuous_subtype_val⟩
  let vw : C(W, V2) :=
    ⟨fun x => (((x : D) : M).2 : V2),
      continuous_subtype_val.comp (continuous_snd.comp
        (continuous_subtype_val.comp continuous_subtype_val))⟩
  have hrw (x : W) : 0 < rw x := hb.trans_le x.property
  let dir : C(W, Q) :=
    ⟨fun x => ⟨(rw x)⁻¹ • vw x, mem_sphere_zero_iff_norm.mpr (by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hrw x)]
      change (rw x)⁻¹ * rw x = 1
      exact inv_mul_cancel₀ (hrw x).ne')⟩,
      ((rw.continuous.inv₀ (fun x => (hrw x).ne')).smul vw.continuous).subtype_mk _⟩
  let boundary : C(W, J × Q) :=
    ⟨fun x => ((((x : D) : M).1), dir x),
      (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).prodMk
        dir.continuous⟩
  let v : C(W, ℝ) := ⟨fun x => min R (2 * rw x - b),
    continuous_const.min ((continuous_const.mul rw.continuous).sub continuous_const)⟩
  have hvb (x : W) : b ≤ v x := by
    exact le_min hbR.le (by have hx := x.property; change b ≤ rw x at hx; linarith)
  have hvR (x : W) : v x ≤ R := min_le_left _ _
  let moved : C(W, D) :=
    ⟨fun x => ⟨((((x : D) : M).1),
      ⟨v x • (dir x : V2), mem_closedBall_zero_iff.mpr (by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hb.le.trans (hvb x)),
          hnorm, mul_one]
        exact hvR x)⟩), fun hx => (not_lt_of_ge (hvb x)) (by
          have hk := hKb _ (hVK hx)
          simpa only [radial, ContinuousMap.coe_mk, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (hb.le.trans (hvb x)), hnorm, mul_one] using hk)⟩,
      (((continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).prodMk
        ((v.continuous.smul dir.continuous.subtype_val).subtype_mk _)).subtype_mk _)⟩
  let mid : C(W, J × Q) :=
    ⟨fun x => (z0, rho (moved x)), continuous_const.prodMk (rho.continuous.comp moved.continuous)⟩
  let time : C(W, ℝ) :=
    ⟨fun x => 2 * (R - rw x) / (R - b),
      ((continuous_const.mul (continuous_const.sub rw.continuous)).div_const _)⟩
  let high : C(W, J × Q) := H.extend.uncurry.comp (time.prodMk boundary)
  let a : ℝ := (R + b) / 2
  have hseam (x : W) (hx : rw x = a) : mid x = high x := by
    have hv : v x = R := by dsimp [v]; rw [hx]; dsimp [a]; apply min_eq_left; linarith
    have ht : time x = 1 := by
      dsimp [time]
      rw [hx]
      dsimp [a]
      field_simp [sub_ne_zero.mpr hbR.ne']
      ring
    have hm : moved x = inc (boundary x) := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        change v x • (dir x : V2) = R • (dir x : V2)
        rw [hv]
    change (z0, rho (moved x)) = H.extend (time x) (boundary x)
    rw [ht, H.extend_one, hm]
    rfl
  let outer : C(W, J × Q) :=
    ⟨fun x => if rw x ≤ a then mid x else high x,
      mid.continuous.if_le high.continuous rw.continuous continuous_const hseam⟩
  have hbase (x : W) (hx : rw x = b) : outer x = (z0, rho (x : D)) := by
    have hba : b ≤ a := by dsimp [a]; linarith
    have hv : v x = b := by
      dsimp [v]
      rw [hx]
      simp only [two_mul, add_sub_cancel_right]
      exact min_eq_right hbR.le
    have hm : moved x = (x : D) := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        change v x • ((rw x)⁻¹ • vw x) = vw x
        rw [hv, hx, smul_smul, mul_inv_cancel₀ hb.ne', one_smul]
    change (if rw x ≤ a then mid x else high x) = _
    rw [if_pos (hx ▸ hba)]
    change (z0, rho (moved x)) = _
    rw [hm]
  let inner : C(low, J × Q) :=
    ⟨fun x => (z0, rho (x : D)),
      continuous_const.prodMk (rho.continuous.comp continuous_subtype_val)⟩
  have hcover : low ∪ W = univ := by
    ext x
    exact iff_true_intro (le_total (radius x) b)
  obtain ⟨r, _, hr⟩ := glue_closed_cover low W
    (isClosed_le radius.continuous continuous_const)
    (isClosed_le continuous_const radius.continuous) hcover inner outer (by
      intro x hx hy
      exact (hbase ⟨x, hy⟩ (le_antisymm hx hy)).symm)
  refine ⟨r, ?_⟩
  intro s u x hxs hxv
  have hrad : radius x = R := by
    change ‖((x : M).2 : V2)‖ = R
    rw [hxv, hRu]
  let xw : W := ⟨x, by change b ≤ radius x; rw [hrad]; exact hbR.le⟩
  have hxwr : rw xw = R := hrad
  have hxa : ¬ rw xw ≤ a := by rw [hxwr]; dsimp [a]; linarith
  have ht : time xw = 0 := by change 2 * (R - rw xw) / (R - b) = 0; rw [hxwr]; simp
  rw [hr xw]
  change (if rw xw ≤ a then mid xw else high xw) = (s, u)
  rw [if_neg hxa]
  change H.extend (time xw) (boundary xw) = (s, u)
  rw [ht, H.extend_zero]
  apply Prod.ext hxs
  apply Subtype.ext
  change (rw xw)⁻¹ • vw xw = (u : V2)
  rw [hxwr]
  change R⁻¹ • ((x : M).2 : V2) = (u : V2)
  rw [hxv, smul_smul, inv_mul_cancel₀ hR.ne', one_smul]

end PoincareConjecture.M76.HamiltonIndexOne
