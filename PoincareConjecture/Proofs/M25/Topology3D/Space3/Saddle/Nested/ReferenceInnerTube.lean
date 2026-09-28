import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceInnerFilling
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.LowerEndTubePrimitives
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HeightCoordinates
import Mathlib.Analysis.Normed.Module.Ball.Pointwise










set_option autoImplicit false

open Set Metric
open scoped ContDiff Pointwise

namespace PoincareConjecture.M25.Topology3D.NestedReferenceLower




theorem exists_inner_reference_tube :
    let U : E2 → ℝ := fun v =>
      ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
    let Q : Set E2 := Metric.closedBall 0 (1 / 2)
    let H : ℝ := 17 / 16
    let delta : ℝ := 1 / 8192
    let B : ℝ := H + delta
    let Omega : Set E2 := {v : E2 | ‖v‖ < 1 / 2 ∧ U v < B}
    let C : E3 ≃L[ℝ] (E2 × ℝ) := heightCoordinates
    ∃ (vmin : E2) (m : ℝ) (e : OpenPartialHomeomorph E2 E2)
      (k : ℝ → ℝ),
      m = U vmin ∧ (63 : ℝ) / 64 ≤ m ∧ m ≤ 1 ∧ e 0 = vmin ∧
      e.source = Metric.ball 0 (Real.sqrt (B - m)) ∧
      e.target = Omega ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ p ∈ e.source, U (e p) = m + ‖p‖ ^ 2) ∧
      (∀ b : ℝ, m ≤ b → b < B →
        e '' Metric.closedBall 0 (Real.sqrt (b - m)) =
          {v : E2 | v ∈ Q ∧ U v ≤ b} ∧
        e '' Metric.ball 0 (Real.sqrt (b - m)) =
          {v : E2 | v ∈ Q ∧ U v < b} ∧
        e '' Metric.sphere 0 (Real.sqrt (b - m)) =
          {v : E2 | v ∈ Q ∧ U v = b}) ∧
      ContDiff ℝ ∞ k ∧
      (∀ z : ℝ, k z ∈ Icc (H - 3 * delta / 4) (H + 3 * delta / 4)) ∧
      EqOn k id (Icc (H - delta / 2) (H + delta / 2)) ∧
      ∀ d : ℝ,
        let r : ℝ → ℝ := fun z => Real.sqrt (k (z - d) - m)
        ∃ T : OpenPartialHomeomorph (E2 × ℝ) E3,
          ContDiff ℝ ∞ r ∧
          (∀ z : ℝ, 0 < r z ∧ r z < Real.sqrt (B - m)) ∧
          (∀ p : E2 × ℝ, T p = C.symm (e (r p.2 • p.1), p.2)) ∧
          (∀ y : E3, T.symm y =
            ((r (C y).2)⁻¹ • e.symm (C y).1, (C y).2)) ∧
          T.source = {p : E2 × ℝ | r p.2 • p.1 ∈ e.source} ∧
          T.target = {y : E3 | (C y).1 ∈ Omega} ∧
          ContDiffOn ℝ ∞ T T.source ∧
          ContDiffOn ℝ ∞ T.symm T.target ∧
          Metric.closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source ∧
          (∀ p : E2 × ℝ, (C (T p)).2 = p.2) ∧
          (∀ y : E3, (T.symm y).2 = (C y).2) ∧
          ∀ z : ℝ, z - d ∈ Icc (H - delta / 2) (H + delta / 2) →
            T '' (Metric.closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
              C.symm '' ({v : E2 | v ∈ Q ∧ U v ≤ z - d} ×ˢ ({z} : Set ℝ)) ∧
            T '' (Metric.ball (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
              C.symm '' ({v : E2 | v ∈ Q ∧ U v < z - d} ×ˢ ({z} : Set ℝ)) ∧
            T '' (Metric.sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
              C.symm '' ({v : E2 | v ∈ Q ∧ U v = z - d} ×ˢ ({z} : Set ℝ)) := by
  classical
  dsimp only
  let U : E2 → ℝ := fun v =>
    ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
  let Q : Set E2 := closedBall 0 (1 / 2)
  let H : ℝ := 17 / 16
  let delta : ℝ := 1 / 8192
  let B : ℝ := H + delta
  let Omega : Set E2 := {v : E2 | ‖v‖ < 1 / 2 ∧ U v < B}
  let C := heightCoordinates
  obtain ⟨vmin, m, e, hm, hlo, hhi, hzero, hsource, htarget, he, hei, hquad, himages⟩ :=
    exists_inner_reference_filling
  change m = U vmin at hm
  change e.source = ball 0 (Real.sqrt (B - m)) at hsource
  change e.target = Omega at htarget
  change ∀ p ∈ e.source, U (e p) = m + ‖p‖ ^ 2 at hquad
  change ∀ b : ℝ, m ≤ b → b < B →
    e '' closedBall 0 (Real.sqrt (b - m)) = {v : E2 | v ∈ Q ∧ U v ≤ b} ∧
    e '' ball 0 (Real.sqrt (b - m)) = {v : E2 | v ∈ Q ∧ U v < b} ∧
    e '' sphere 0 (Real.sqrt (b - m)) = {v : E2 | v ∈ Q ∧ U v = b} at himages
  obtain ⟨k, hk, hkrange, hkid⟩ := exists_saddle_end_height_clamp
    (H - delta / 2) (H + delta / 2) (delta / 4)
    (by dsimp [H, delta]; norm_num) (by dsimp [delta]; norm_num)
  have hkr (z : ℝ) : k z ∈ Icc (H - 3 * delta / 4) (H + 3 * delta / 4) := by
    have hh := hkrange z
    constructor <;> linarith only [hh.1, hh.2]
  refine ⟨vmin, m, e, k, hm, hlo, hhi, hzero, hsource, htarget, he, hei,
    hquad, himages, hk, hkr, hkid, ?_⟩
  intro d
  let r : ℝ → ℝ := fun z => Real.sqrt (k (z - d) - m)
  have harg (z : ℝ) : 0 < k (z - d) - m := by
    have hh := (hkr (z - d)).1
    dsimp only [H, delta] at hh
    linarith only [hh, hhi]
  have hargB (z : ℝ) : k (z - d) < B := by
    have hh := (hkr (z - d)).2
    dsimp only [H, delta, B] at hh ⊢
    linarith only [hh]
  have hr : ContDiff ℝ ∞ r :=
    ((hk.comp (contDiff_id.sub contDiff_const)).sub contDiff_const).sqrt
      (fun z => (harg z).ne')
  have hrb (z : ℝ) : 0 < r z ∧ r z < Real.sqrt (B - m) :=
    ⟨Real.sqrt_pos.mpr (harg z),
      Real.sqrt_lt_sqrt (harg z).le (sub_lt_sub_right (hargB z) m)⟩
  have hri : ContDiff ℝ ∞ (fun z => (r z)⁻¹) := hr.inv (fun z => (hrb z).1.ne')
  let S : Set (E2 × ℝ) := {p | r p.2 • p.1 ∈ e.source}
  let V : Set E3 := {y | (C y).1 ∈ Omega}
  let f : E2 × ℝ → E3 := fun p => C.symm (e (r p.2 • p.1), p.2)
  let g : E3 → E2 × ℝ := fun y => ((r (C y).2)⁻¹ • e.symm (C y).1, (C y).2)
  have ha : ContDiff ℝ ∞ (fun p : E2 × ℝ => r p.2 • p.1) :=
    (hr.comp contDiff_snd).smul contDiff_fst
  have hS : IsOpen S := e.open_source.preimage ha.continuous
  have hV : IsOpen V := (htarget ▸ e.open_target).preimage C.continuous.fst
  have hf : ContDiffOn ℝ ∞ f S := C.symm.contDiff.comp_contDiffOn
    ((he.comp ha.contDiffOn (fun _ hp => hp)).prodMk contDiff_snd.contDiffOn)
  have hg : ContDiffOn ℝ ∞ g V :=
    (((hri.comp C.contDiff.snd).contDiffOn).smul
      (hei.comp C.contDiff.fst.contDiffOn (fun _ hy => htarget.symm ▸ hy))).prodMk
        C.contDiff.snd.contDiffOn
  have hmapf (p : E2 × ℝ) (hp : p ∈ S) : f p ∈ V := by
    change (C (C.symm (e (r p.2 • p.1), p.2))).1 ∈ Omega
    rw [C.apply_symm_apply, ← htarget]
    exact e.map_source hp
  have hmapg (y : E3) (hy : y ∈ V) : g y ∈ S := by
    change r (C y).2 • ((r (C y).2)⁻¹ • e.symm (C y).1) ∈ e.source
    rw [smul_smul, mul_inv_cancel₀ (hrb _).1.ne', one_smul]
    exact e.map_target (htarget.symm ▸ hy)
  have hgf (p : E2 × ℝ) (hp : p ∈ S) : g (f p) = p := by
    dsimp only [g, f]
    rw [C.apply_symm_apply, e.left_inv hp, smul_smul,
      inv_mul_cancel₀ (hrb _).1.ne', one_smul]
  have hfg (y : E3) (hy : y ∈ V) : f (g y) = y := by
    dsimp only [f, g]
    rw [smul_smul, mul_inv_cancel₀ (hrb _).1.ne', one_smul,
      e.right_inv (htarget.symm ▸ hy), Prod.eta, C.symm_apply_apply]
  let T : OpenPartialHomeomorph (E2 × ℝ) E3 :=
    { toFun := f
      invFun := g
      source := S
      target := V
      map_source' := hmapf
      map_target' := hmapg
      left_inv' := hgf
      right_inv' := hfg
      continuousOn_toFun := hf.continuousOn
      continuousOn_invFun := hg.continuousOn
      open_source := hS
      open_target := hV }
  have hclosed : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source := by
    rintro ⟨x, z⟩ ⟨hx, _hz⟩
    change r z • x ∈ e.source
    rw [hsource, mem_ball_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (hrb z).1]
    exact (mul_le_of_le_one_right (hrb z).1.le (mem_closedBall_zero_iff.mp hx)).trans_lt
      (hrb z).2
  have hheight (p : E2 × ℝ) : (C (T p)).2 = p.2 := by
    change (C (C.symm (e (r p.2 • p.1), p.2))).2 = p.2
    rw [C.apply_symm_apply]
  refine ⟨T, hr, hrb, fun _ => rfl, fun _ => rfl, rfl, rfl, hf, hg,
    hclosed, hheight, fun _ => rfl, ?_⟩
  intro z hz
  change z - d ∈ Icc (H - delta / 2) (H + delta / 2) at hz
  have hmb : m < z - d := by
    have hh := hz.1
    dsimp only [H, delta] at hh
    linarith only [hh, hhi]
  have hbB : z - d < B := by
    have hh := hz.2
    dsimp only [H, delta, B] at hh ⊢
    linarith only [hh]
  have hrz : r z = Real.sqrt (z - d - m) := by
    dsimp only [r]
    rw [hkid hz]
    rfl
  have hslices := himages (z - d) hmb.le hbB
  have hslice (D0 : Set E2) : T '' (D0 ×ˢ ({z} : Set ℝ)) =
      C.symm '' ((e '' (r z • D0)) ×ˢ ({z} : Set ℝ)) := by
    ext y
    constructor
    · rintro ⟨⟨x, w⟩, ⟨hx, hw⟩, rfl⟩
      have hw' : w = z := hw
      subst w
      exact ⟨(e (r z • x), z), ⟨⟨r z • x, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨⟨v, w⟩, ⟨⟨p, hp, hpv⟩, hw⟩, rfl⟩
      obtain ⟨x, hx, hxp⟩ := hp
      have hw' : w = z := hw
      subst w
      subst p
      change e (r z • x) = v at hpv
      subst v
      exact ⟨(x, z), ⟨hx, rfl⟩, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hslice, smul_unitClosedBall_of_nonneg (hrb z).1.le, hrz, hslices.1]
  · rw [hslice, smul_unitBall_of_pos (hrb z).1, hrz, hslices.2.1]
  · rw [hslice, smul_sphere' (hrb z).1.ne', smul_zero, Real.norm_eq_abs,
      abs_of_pos (hrb z).1, mul_one, hrz, hslices.2.2]

end PoincareConjecture.M25.Topology3D.NestedReferenceLower
