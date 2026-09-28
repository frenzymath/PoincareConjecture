import PoincareConjecture.Proofs.M25.Topology3D.Services
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CompactSmoothChart
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_saddle_planar_curve_normal_chart
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (gamma : ℝ → E2) (a b l r : ℝ)
    (hal : a < l) (hlr : l ≤ r) (hrb : r < b)
    (hgamma : ContDiffOn ℝ ∞ gamma (Ioo a b))
    (hinj : Set.InjOn gamma (Ioo a b))
    (hreg : ∀ t ∈ Ioo a b, deriv gamma t ≠ 0)
    (O : Set E2) (hO : IsOpen O)
    (himage : gamma '' Icc l r ⊆ O) :
    let rot : E2 → E2 := fun v => J2.symm (-(J2 v).2, (J2 v).1)
    ∃ (w : ℝ) (N : OpenPartialHomeomorph (ℝ × ℝ) E2),
      0 < w ∧ Icc l r ×ˢ Icc (-w) w ⊆ N.source ∧
      N.source ⊆ Ioo a b ×ˢ (univ : Set ℝ) ∧ N.target ⊆ O ∧
      ContDiffOn ℝ ∞ N N.source ∧
      ContDiffOn ℝ ∞ N.symm N.target ∧
      ∀ p ∈ N.source,
        N p = gamma p.1 + p.2 • rot (deriv gamma p.1) := by
  classical
  let rot : E2 → E2 := fun v => J2.symm (-(J2 v).2, (J2 v).1)
  let x : ℝ → ℝ := fun t => (J2 (gamma t)).1
  let y : ℝ → ℝ := fun t => (J2 (gamma t)).2
  let dx : ℝ → ℝ := fun t => (J2 (deriv gamma t)).1
  let dy : ℝ → ℝ := fun t => (J2 (deriv gamma t)).2
  let f : ℝ × ℝ → ℝ × ℝ := fun p =>
    (x p.1 - p.2 * dy p.1, y p.1 + p.2 * dx p.1)
  let g : ℝ × ℝ → E2 := fun p => J2.symm (f p)
  let V : Set (ℝ × ℝ) := Ioo a b ×ˢ univ
  let Q : Set (ℝ × ℝ) := Icc l r ×ˢ {0}
  have hV : IsOpen V := isOpen_Ioo.prod isOpen_univ
  have hQ : IsCompact Q := isCompact_Icc.prod isCompact_singleton
  have hI {t : ℝ} (ht : t ∈ Icc l r) : t ∈ Ioo a b :=
    ordConnected_Ioo.out ⟨hal, hlr.trans_lt hrb⟩ ⟨hal.trans_le hlr, hrb⟩ ht
  have hdgamma : ContDiffOn ℝ ∞ (deriv gamma) (Ioo a b) :=
    ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo).mp hgamma).2
  have hxy (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt x (dx t) t ∧ HasDerivAt y (dy t) t := by
    have hd := ((hgamma.contDiffAt (isOpen_Ioo.mem_nhds ht)).differentiableAt
      (by simp)).hasDerivAt
    have he := J2.hasFDerivAt.comp_hasDerivAt t hd
    exact ⟨he.fst, he.snd⟩
  have hdx (t : ℝ) (ht : t ∈ Ioo a b) :
      ContDiffAt ℝ ∞ dx t ∧ ContDiffAt ℝ ∞ dy t := by
    have hd := J2.contDiff.contDiffAt.comp t
      (hdgamma.contDiffAt (isOpen_Ioo.mem_nhds ht))
    exact ⟨hd.fst, hd.snd⟩
  have hf : ContDiffOn ℝ ∞ f V := by
    intro p hp
    have h0 := J2.contDiff.contDiffAt.comp p
      ((hgamma.contDiffAt (isOpen_Ioo.mem_nhds hp.1)).comp p contDiffAt_fst)
    have h1 := (hdx p.1 hp.1).1.comp p contDiffAt_fst
    have h2 := (hdx p.1 hp.1).2.comp p contDiffAt_fst
    exact ((h0.fst.sub (contDiffAt_snd.mul h2)).prodMk
      (h0.snd.add (contDiffAt_snd.mul h1))).contDiffWithinAt
  have hg : ContDiffOn ℝ ∞ g V := by
    intro p hp
    exact (J2.symm.contDiff.contDiffAt.comp p
      (hf.contDiffAt (hV.mem_nhds hp))).contDiffWithinAt
  have hf0 (t : ℝ) : f (t, 0) = J2 (gamma t) := by
    apply Prod.ext <;> simp [f, x, y]
  have hg0 (t : ℝ) : g (t, 0) = gamma t := by
    simp only [g, hf0, J2.symm_apply_apply]
  let D : Set (ℝ × ℝ) := V ∩ g ⁻¹' O
  have hD : IsOpen D := hg.continuousOn.isOpen_inter_preimage hV hO
  have hQD : Q ⊆ D := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    refine ⟨⟨hI ht, mem_univ _⟩, ?_⟩
    change g (t, 0) ∈ O
    rw [hg0]
    exact himage ⟨t, ht, rfl⟩
  have hfi : InjOn f Q := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩ ⟨t', s'⟩ ⟨ht', hs'⟩ he
    have hs0 : s = 0 := hs
    have hs'0 : s' = 0 := hs'
    subst s
    subst s'
    rw [hf0, hf0] at he
    exact Prod.ext (hinj (hI ht) (hI ht') (J2.injective he)) rfl
  have hfd (p : ℝ × ℝ) (hp : p ∈ Q) :
      ∃ A : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ), HasFDerivAt f (A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p := by
    rcases p with ⟨t, s⟩
    have hs : s = 0 := hp.2
    subst s
    have ht := hI hp.1
    let d : ℝ := dx t ^ 2 + dy t ^ 2
    have hd : d ≠ 0 := by
      intro hd
      change dx t ^ 2 + dy t ^ 2 = 0 at hd
      have hx0 : dx t = 0 := by nlinarith [sq_nonneg (dy t)]
      have hy0 : dy t = 0 := by nlinarith [sq_nonneg (dx t)]
      apply hreg t ht
      apply J2.injective
      apply Prod.ext
      · simpa only [map_zero, Prod.fst_zero] using hx0
      · simpa only [map_zero, Prod.snd_zero] using hy0
    let A : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) := {
      toFun := fun p => (dx t * p.1 - dy t * p.2, dy t * p.1 + dx t * p.2)
      invFun := fun p => ((dx t * p.1 + dy t * p.2) / d,
        (-dy t * p.1 + dx t * p.2) / d)
      map_add' := by intro p q; apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
      map_smul' := by
        intro c p
        apply Prod.ext
        · change dx t * (c * p.1) - dy t * (c * p.2) = c * (dx t * p.1 - dy t * p.2)
          ring
        · change dy t * (c * p.1) + dx t * (c * p.2) = c * (dy t * p.1 + dx t * p.2)
          ring
      left_inv := by
        intro p
        apply Prod.ext <;> dsimp only <;> field_simp [hd] <;> dsimp [d] <;> ring
      right_inv := by
        intro p
        apply Prod.ext <;> dsimp only <;> field_simp [hd] <;> dsimp [d] <;> ring
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
    have hfst : HasFDerivAt (Prod.fst : ℝ × ℝ → ℝ)
        (ContinuousLinearMap.fst ℝ ℝ ℝ) (t, 0) := hasFDerivAt_fst
    have hsnd : HasFDerivAt (Prod.snd : ℝ × ℝ → ℝ)
        (ContinuousLinearMap.snd ℝ ℝ ℝ) (t, 0) := hasFDerivAt_snd
    have hdx' := ((hdx t ht).1.differentiableAt (by simp)).hasFDerivAt.comp
      (t, (0 : ℝ)) hfst
    have hdy' := ((hdx t ht).2.differentiableAt (by simp)).hasFDerivAt.comp
      (t, (0 : ℝ)) hfst
    have hx' := (hxy t ht).1.comp_hasFDerivAt (t, (0 : ℝ)) hfst
    have hy' := (hxy t ht).2.comp_hasFDerivAt (t, (0 : ℝ)) hfst
    have hleft := hx'.sub (hsnd.mul hdy')
    have hright := hy'.add (hsnd.mul hdx')
    refine ⟨A, ?_⟩
    convert! hleft.prodMk hright using 1
    ext <;> simp [A]
  obtain ⟨e, he, hQe, heD, hes, hei⟩ := exists_smoothChart_near_compact f
    hQ hD hQD (hf.mono inter_subset_left) hfi hfd
  let N : OpenPartialHomeomorph (ℝ × ℝ) E2 :=
    e.trans J2.symm.toHomeomorph.toOpenPartialHomeomorph
  have hNs {p : ℝ × ℝ} : p ∈ N.source ↔ p ∈ e.source := by
    change (p ∈ e.source ∧ e p ∈ (univ : Set (ℝ × ℝ))) ↔ p ∈ e.source
    simp only [mem_univ, and_true]
  have hNp (p : ℝ × ℝ) : N p = g p := by
    change J2.symm (e p) = J2.symm (f p)
    rw [he]
  have hNQ : Q ⊆ N.source := fun p hp => hNs.mpr (hQe hp)
  have hNV : N.source ⊆ V := fun _ hp => (heD (hNs.mp hp)).1
  have hNO : N.target ⊆ O := by
    intro y hy
    obtain ⟨p, hp, hpy⟩ := N.surjOn hy
    have hgO : g p ∈ O := (heD (hNs.mp hp)).2
    rwa [← hNp, hpy] at hgO
  have hNsm : ContDiffOn ℝ ∞ N N.source := by
    intro p hp
    have hne := hes.contDiffAt (e.open_source.mem_nhds (hNs.mp hp))
    exact (J2.symm.contDiff.contDiffAt.comp p hne).contDiffWithinAt
  have hNinv : ContDiffOn ℝ ∞ N.symm N.target := by
    intro y hy
    have hyt : J2 y ∈ e.target := hy.2
    have hne := hei.contDiffAt (e.open_target.mem_nhds hyt)
    exact (hne.comp y J2.contDiff.contDiffAt).contDiffWithinAt
  obtain ⟨delta, hdelta, hdsub⟩ := hQ.exists_thickening_subset_open N.open_source hNQ
  let w : ℝ := delta / 2
  have hw : 0 < w := by dsimp [w]; positivity
  refine ⟨w, N, hw, ?_, hNV, hNO, hNsm, hNinv, ?_⟩
  · rintro ⟨t, s⟩ ⟨ht, hs⟩
    apply hdsub
    apply mem_thickening_iff.mpr
    refine ⟨(t, 0), ⟨ht, mem_singleton _⟩, ?_⟩
    rw [dist_prod_same_left, Real.dist_eq, sub_zero]
    have hsw : |s| ≤ w := abs_le.mpr hs
    dsimp [w] at hsw
    linarith
  · intro p _hp
    change N p = gamma p.1 + p.2 • rot (deriv gamma p.1)
    rw [hNp]
    apply J2.injective
    simp only [g, J2.apply_symm_apply, f, x, y, dx, dy,
      map_add, map_smul, rot, Prod.smul_mk, smul_eq_mul]
    apply Prod.ext
    · change x p.1 - p.2 * dy p.1 = x p.1 + p.2 * (-dy p.1)
      ring
    · rfl

end PoincareConjecture.M25.Topology3D
