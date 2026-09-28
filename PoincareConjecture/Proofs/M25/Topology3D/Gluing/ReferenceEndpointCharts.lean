import PoincareConjecture.Proofs.M25.Topology3D.Services
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Tactic










set_option autoImplicit false

open Set
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D




theorem exists_reference_endpoint_charts_of_coordinates
    (rho delta : ℝ) (hrho : 0 < rho)
    (e : OpenPartialHomeomorph UnitTwoSphere (ℝ × ℝ))
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target)
    (hbuffer : {v : ℝ × ℝ | v.1 ^ 2 + v.2 ^ 2 < (2 * rho) ^ 2} ⊆ e.target)
    (X : Fin 4 → OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ))
    (hXsource : ∀ i : Fin 4, (X i).source =
      Ioo (-2 * delta) (2 * delta) ×ˢ Ioo (-(1 / 8) : ℝ) (1 / 8))
    (hX : ∀ i : Fin 4, ContDiffOn ℝ ∞ (X i) (X i).source)
    (hXi : ∀ i : Fin 4, ContDiffOn ℝ ∞ (X i).symm (X i).target)
    (hXformula : ∀ (i : Fin 4) (w : ℝ × ℝ), w ∈ (X i).source →
      ((X i) w).1 ^ 2 + ((X i) w).2 ^ 2 = rho ^ 2 * (1 + w.2) ^ 2 ∧
      -((X i) w).1 ^ 2 + ((X i) w).2 ^ 2 = w.1)
    (f : UnitTwoSphere → ℝ)
    (hf : ∀ p ∈ e.source, f p = -(e p).1 ^ 2 + (e p).2 ^ 2) :
    let U : Set (ℝ × ℝ) :=
      Ioo (-2 * delta) (2 * delta) ×ˢ Ioo (-(1 / 8) : ℝ) (1 / 8)
    let Dc : Set UnitTwoSphere := e.symm ''
      {v : ℝ × ℝ | v.1 ^ 2 + v.2 ^ 2 ≤ rho ^ 2}
    let Do : Set UnitTwoSphere := e.symm ''
      {v : ℝ × ℝ | v.1 ^ 2 + v.2 ^ 2 < rho ^ 2}
    ∃ E : Fin 4 → OpenPartialHomeomorph (ℝ × ℝ) UnitTwoSphere,
      ∀ i : Fin 4,
        (E i).source = U ∧ (E i).target ⊆ e.source ∧
        ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ (E i) (E i).source ∧
        ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ (E i).symm (E i).target ∧
        (∀ w : ℝ × ℝ, E i w = e.symm (X i w)) ∧
        (∀ p : UnitTwoSphere, (E i).symm p = (X i).symm (e p)) ∧
        (∀ p ∈ (E i).target, ((E i).symm p).1 = f p) ∧
        (∀ w ∈ U, f (E i w) = w.1) ∧
        (∀ w ∈ U, E i w ∈ Dc ↔ w.2 ≤ 0) ∧
        (∀ w ∈ U, E i w ∈ Do ↔ w.2 < 0) := by
  intro U Dc Do
  have hrho2 : 0 < rho ^ 2 := sq_pos_of_pos hrho
  have hsecond (i : Fin 4) (w : ℝ × ℝ) (hw : w ∈ (X i).source) :
      -(1 / 8 : ℝ) < w.2 ∧ w.2 < 1 / 8 := by
    rw [hXsource i] at hw
    exact hw.2
  have hXinto (i : Fin 4) : MapsTo (X i) (X i).source e.target := by
    intro w hw
    apply hbuffer
    change ((X i) w).1 ^ 2 + ((X i) w).2 ^ 2 < (2 * rho) ^ 2
    rw [(hXformula i w hw).1]
    have ha := hsecond i w hw
    have hp : 0 < (2 - (1 + w.2)) * (2 + (1 + w.2)) :=
      mul_pos (by linarith only [ha.2]) (by linarith only [ha.1])
    have hs : (1 + w.2) ^ 2 < 4 := by nlinarith only [hp]
    have hm := mul_lt_mul_of_pos_left hs hrho2
    nlinarith only [hm]
  have hdisc (v : ℝ × ℝ) (hv : v.1 ^ 2 + v.2 ^ 2 ≤ rho ^ 2) :
      v ∈ e.target := by
    apply hbuffer
    change v.1 ^ 2 + v.2 ^ 2 < (2 * rho) ^ 2
    nlinarith only [hv, hrho2]
  let E : Fin 4 → OpenPartialHomeomorph (ℝ × ℝ) UnitTwoSphere := fun i =>
    (X i).trans e.symm
  have hESource (i : Fin 4) : (E i).source = U := by
    change ((X i).trans e.symm).source = U
    rw [OpenPartialHomeomorph.trans_source]
    exact (inter_eq_left.mpr (hXinto i)).trans (hXsource i)
  have hETarget (i : Fin 4) (p : UnitTwoSphere) (hp : p ∈ (E i).target) :
      p ∈ e.source ∧ e p ∈ (X i).target := hp
  have hsource (i : Fin 4) (w : ℝ × ℝ) (hw : w ∈ U) : w ∈ (X i).source := by
    rw [hXsource i]
    exact hw
  have hcoord (i : Fin 4) (w : ℝ × ℝ) (hw : w ∈ U) : e (E i w) = X i w :=
    e.right_inv (hXinto i (hsource i w hw))
  have hHeight (i : Fin 4) (w : ℝ × ℝ) (hw : w ∈ U) : f (E i w) = w.1 := by
    have hmem : E i w ∈ e.source := e.map_target (hXinto i (hsource i w hw))
    rw [hf _ hmem, hcoord i w hw]
    exact (hXformula i w (hsource i w hw)).2
  have hclosed (a : ℝ) (ha : -1 < a) :
      rho ^ 2 * (1 + a) ^ 2 ≤ rho ^ 2 ↔ a ≤ 0 := by
    have hcancel : rho ^ 2 * (1 + a) ^ 2 ≤ rho ^ 2 ↔ (1 + a) ^ 2 ≤ 1 := by
      simpa only [mul_one] using
        (mul_le_mul_iff_right₀ hrho2 : rho ^ 2 * (1 + a) ^ 2 ≤ rho ^ 2 * 1 ↔ _)
    rw [hcancel]
    constructor
    · intro hs
      nlinarith only [hs, sq_nonneg a]
    · intro ha0
      have hp := mul_nonpos_of_nonpos_of_nonneg ha0 (show 0 ≤ a + 2 by linarith)
      nlinarith only [hp]
  have hopen (a : ℝ) (ha : -1 < a) :
      rho ^ 2 * (1 + a) ^ 2 < rho ^ 2 ↔ a < 0 := by
    have hcancel : rho ^ 2 * (1 + a) ^ 2 < rho ^ 2 ↔ (1 + a) ^ 2 < 1 := by
      simpa only [mul_one] using
        (mul_lt_mul_iff_right₀ hrho2 : rho ^ 2 * (1 + a) ^ 2 < rho ^ 2 * 1 ↔ _)
    rw [hcancel]
    constructor
    · intro hs
      nlinarith only [hs, sq_nonneg a]
    · intro ha0
      have hp := mul_neg_of_neg_of_pos ha0 (show 0 < a + 2 by linarith)
      nlinarith only [hp]
  refine ⟨E, fun i => ⟨hESource i, fun p hp => (hETarget i p hp).1,
    ?_, ?_, fun _ => rfl, fun _ => rfl, ?_, hHeight i, ?_, ?_⟩⟩
  · rw [hESource i]
    exact hei.comp ((hX i).contMDiffOn.mono (fun w hw => hsource i w hw))
      (fun w hw => hXinto i (hsource i w hw))
  · exact (hXi i).contMDiffOn.comp
      (he.mono (fun p hp => (hETarget i p hp).1))
      (fun p hp => (hETarget i p hp).2)
  · intro p hp
    have hw : (E i).symm p ∈ U := hESource i ▸ (E i).map_target hp
    simpa only [(E i).right_inv hp] using (hHeight i ((E i).symm p) hw).symm
  · intro w hw
    have hwX := hsource i w hw
    have ha : -1 < w.2 := by linarith only [(hsecond i w hwX).1]
    constructor
    · rintro ⟨v, hv, heq⟩
      have hvEq : v = X i w :=
        e.symm.injOn (hdisc v hv) (hXinto i hwX) heq
      have hn : ((X i) w).1 ^ 2 + ((X i) w).2 ^ 2 ≤ rho ^ 2 := hvEq ▸ hv
      rw [(hXformula i w hwX).1] at hn
      exact (hclosed w.2 ha).mp hn
    · intro ha0
      refine ⟨X i w, ?_, rfl⟩
      change ((X i) w).1 ^ 2 + ((X i) w).2 ^ 2 ≤ rho ^ 2
      rw [(hXformula i w hwX).1]
      exact (hclosed w.2 ha).mpr ha0
  · intro w hw
    have hwX := hsource i w hw
    have ha : -1 < w.2 := by linarith only [(hsecond i w hwX).1]
    constructor
    · rintro ⟨v, hv, heq⟩
      have hvEq : v = X i w :=
        e.symm.injOn (hdisc v hv.le) (hXinto i hwX) heq
      have hn : ((X i) w).1 ^ 2 + ((X i) w).2 ^ 2 < rho ^ 2 := hvEq ▸ hv
      rw [(hXformula i w hwX).1] at hn
      exact (hopen w.2 ha).mp hn
    · intro ha0
      refine ⟨X i w, ?_, rfl⟩
      change ((X i) w).1 ^ 2 + ((X i) w).2 ^ 2 < rho ^ 2
      rw [(hXformula i w hwX).1]
      exact (hopen w.2 ha).mpr ha0

end PoincareConjecture.M25.Topology3D
