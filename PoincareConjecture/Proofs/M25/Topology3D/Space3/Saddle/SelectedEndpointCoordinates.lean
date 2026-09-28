import PoincareConjecture.Definitions.Ch09.RoundCylinderGeometry
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.EndpointReparametrization
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false

open Set Function Filter Metric
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_saddle_selected_endpoint_coordinates
    (delta eta0 : ℝ) (hdelta : 0 < delta) (heta0 : 0 < eta0)
    (E : Fin 4 → OpenPartialHomeomorph (ℝ × ℝ) UnitTwoSphere)
    (hSource : ∀ a : Fin 4,
      (E a).source = Ioo (-2 * delta) (2 * delta) ×ˢ
        Ioo (-(1 / 8) : ℝ) (1 / 8))
    (hE : ∀ a : Fin 4,
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ (E a) (E a).source)
    (hEinv : ∀ a : Fin 4,
      ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ (E a).symm (E a).target)
    (f : UnitTwoSphere → ℝ)
    (hFirst : ∀ (a : Fin 4) (p : UnitTwoSphere), p ∈ (E a).target →
      ((E a).symm p).1 = f p)
    (Dc : Set UnitTwoSphere)
    (hClosed : ∀ (a : Fin 4) (w : ℝ × ℝ), w ∈ (E a).source →
      (E a w ∈ Dc ↔ w.2 ≤ 0))
    (alpha : Fin 2 → ℝ → UnitTwoSphere)
    (hAlpha : ∀ i : Fin 2, ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ (alpha i))
    (hReg : ∀ (i : Fin 2) (t : ℝ),
      Function.Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (alpha i) t))
    (hLevel : ∀ (i : Fin 2) (t : ℝ), f (alpha i t) = -delta)
    (hEnds : ∀ i : Fin 2,
      alpha i 0 = E (finProdFinEquiv (i, (0 : Fin 2))) (-delta, 0) ∧
      alpha i 1 = E (finProdFinEquiv (i, (1 : Fin 2))) (-delta, 0))
    (hExterior : ∀ (i : Fin 2) (t : ℝ), t ∈ Ioo (0 : ℝ) 1 →
      alpha i t ∉ Dc)
    (hAfter : ∀ (i : Fin 2) (t : ℝ), t ∈ Ioo (1 : ℝ) (1 + eta0) →
      alpha i t ∈ Dc) :
    let b0 : Fin 2 → ℝ → ℝ := fun i t =>
      ((E (finProdFinEquiv (i, (0 : Fin 2)))).symm (alpha i t)).2
    let b1 : Fin 2 → ℝ → ℝ := fun i t =>
      ((E (finProdFinEquiv (i, (1 : Fin 2)))).symm (alpha i t)).2
    ∃ eta : ℝ, 0 < eta ∧ eta < eta0 ∧ eta < 1 / 8 ∧
      ∀ i : Fin 2,
        MapsTo (alpha i) (Ioo (-eta) eta)
          (E (finProdFinEquiv (i, (0 : Fin 2)))).target ∧
        MapsTo (alpha i) (Ioo (1 - eta) (1 + eta))
          (E (finProdFinEquiv (i, (1 : Fin 2)))).target ∧
        ContDiffOn ℝ ∞ (b0 i) (Ioo (-eta) eta) ∧
        ContDiffOn ℝ ∞ (b1 i) (Ioo (1 - eta) (1 + eta)) ∧
        b0 i 0 = 0 ∧ b1 i 1 = 0 ∧
        0 < deriv (b0 i) 0 ∧ 0 < deriv (fun t => 1 - b1 i t) 1 ∧
        (∀ t ∈ Ioo (-eta) eta,
          (E (finProdFinEquiv (i, (0 : Fin 2)))).symm (alpha i t) =
            (-delta, b0 i t) ∧
          E (finProdFinEquiv (i, (0 : Fin 2))) (-delta, b0 i t) = alpha i t ∧
          b0 i t ∈ Ioo (-(1 / 8) : ℝ) (1 / 8)) ∧
        (∀ t ∈ Ioo (1 - eta) (1 + eta),
          (E (finProdFinEquiv (i, (1 : Fin 2)))).symm (alpha i t) =
            (-delta, b1 i t) ∧
          E (finProdFinEquiv (i, (1 : Fin 2))) (-delta, b1 i t) = alpha i t ∧
          b1 i t ∈ Ioo (-(1 / 8) : ℝ) (1 / 8)) := by
  classical
  intro b0 b1
  have hcenter (a : Fin 4) : (-delta, (0 : ℝ)) ∈ (E a).source := by
    rw [hSource]
    exact ⟨⟨by linarith, by linarith⟩, by norm_num⟩
  have hlocal (i : Fin 2) (a : Fin 4) (t0 : ℝ)
      (hend : alpha i t0 = E a (-delta, 0)) :
      ∃ r : ℝ, 0 < r ∧
        MapsTo (alpha i) (Ioo (t0 - r) (t0 + r)) (E a).target := by
    have ht : alpha i t0 ∈ (E a).target := by
      rw [hend]
      exact (E a).map_source (hcenter a)
    have hn : ∀ᶠ t in 𝓝 t0, alpha i t ∈ (E a).target :=
      (hAlpha i).continuous.continuousAt.eventually ((E a).open_target.mem_nhds ht)
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hn
    refine ⟨r, hr, ?_⟩
    intro t ht
    apply hball
    rw [Real.dist_eq]
    exact abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hwindow (i : Fin 2) : ∃ r : ℝ, 0 < r ∧
      MapsTo (alpha i) (Ioo (-r) r)
        (E (finProdFinEquiv (i, (0 : Fin 2)))).target ∧
      MapsTo (alpha i) (Ioo (1 - r) (1 + r))
        (E (finProdFinEquiv (i, (1 : Fin 2)))).target := by
    obtain ⟨r0, hr0, hm0⟩ := hlocal i _ 0 (hEnds i).1
    obtain ⟨r1, hr1, hm1⟩ := hlocal i _ 1 (hEnds i).2
    simp only [zero_sub, zero_add] at hm0
    refine ⟨min r0 r1, lt_min hr0 hr1, ?_, ?_⟩
    · intro t ht
      exact hm0 ⟨by linarith [ht.1, min_le_left r0 r1],
        lt_of_lt_of_le ht.2 (min_le_left r0 r1)⟩
    · intro t ht
      exact hm1 ⟨by linarith [ht.1, min_le_right r0 r1],
        by linarith [ht.2, min_le_right r0 r1]⟩
  choose r hr hm0 hm1 using hwindow
  let eta : ℝ := min (min eta0 (1 / 8)) (min (r 0) (r 1)) / 2
  have hmin : 0 < min (min eta0 (1 / 8)) (min (r 0) (r 1)) :=
    lt_min (lt_min heta0 (by norm_num)) (lt_min (hr 0) (hr 1))
  have heta : 0 < eta := half_pos hmin
  have hemin : eta < min (min eta0 (1 / 8)) (min (r 0) (r 1)) :=
    div_lt_self hmin (by norm_num)
  have hebase : eta < min eta0 (1 / 8) := hemin.trans_le (min_le_left _ _)
  have heradius : eta < min (r 0) (r 1) := hemin.trans_le (min_le_right _ _)
  have he0 : eta < eta0 := hebase.trans_le (min_le_left _ _)
  have heSmall : eta < 1 / 8 := hebase.trans_le (min_le_right _ _)
  have her (i : Fin 2) : eta ≤ r i := by
    fin_cases i
    · exact heradius.le.trans (min_le_left _ _)
    · exact heradius.le.trans (min_le_right _ _)
  have hcoords (i : Fin 2) (a : Fin 4) (t : ℝ) (ht : alpha i t ∈ (E a).target) :
      (E a).symm (alpha i t) = (-delta, ((E a).symm (alpha i t)).2) ∧
      E a (-delta, ((E a).symm (alpha i t)).2) = alpha i t ∧
      ((E a).symm (alpha i t)).2 ∈ Ioo (-(1 / 8) : ℝ) (1 / 8) := by
    have he : (E a).symm (alpha i t) = (-delta, ((E a).symm (alpha i t)).2) :=
      Prod.ext ((hFirst a _ ht).trans (hLevel i t)) rfl
    have hs := (E a).map_target ht
    rw [hSource] at hs
    refine ⟨he, ?_, hs.2⟩
    rw [← he]
    exact (E a).right_inv ht
  have hclosedAt (i : Fin 2) (a : Fin 4) (t : ℝ) (ht : alpha i t ∈ (E a).target) :
      alpha i t ∈ Dc ↔ ((E a).symm (alpha i t)).2 ≤ 0 := by
    simpa only [(E a).right_inv ht] using
      hClosed a ((E a).symm (alpha i t)) ((E a).map_target ht)
  have hnonzero (i : Fin 2) (a : Fin 4) (t : ℝ) (ht : alpha i t ∈ (E a).target) :
      deriv (fun s : ℝ => ((E a).symm (alpha i s)).2) t ≠ 0 := by
    let F : ℝ → ℝ × ℝ := fun s => (E a).symm (alpha i s)
    have hED : (E a).MDifferentiable 𝓘(ℝ, ℝ × ℝ) (𝓡 2) :=
      ⟨(hE a).mdifferentiableOn (by simp), (hEinv a).mdifferentiableOn (by simp)⟩
    have hFs : ContDiffAt ℝ ∞ F t :=
      (((hEinv a).contMDiffAt ((E a).open_target.mem_nhds ht)).comp t
        (hAlpha i).contMDiffAt).contDiffAt
    have hinj : Injective (fderiv ℝ F t) := by
      change Injective (fderiv ℝ ((E a).symm ∘ alpha i) t)
      rw [← mfderiv_eq_fderiv, mfderiv_comp t
        (hED.mdifferentiableAt_symm ht) ((hAlpha i).mdifferentiable (by simp) t)]
      exact (hED.symm.mfderiv_injective ht).comp (hReg i t)
    have heq : F =ᶠ[𝓝 t] (fun s => (-delta, (F s).2)) := by
      filter_upwards [(hAlpha i).continuous.continuousAt.eventually
        ((E a).open_target.mem_nhds ht)] with s hs
      exact (hcoords i a s hs).1
    have hpair : HasDerivAt (fun s : ℝ => (-delta, (F s).2))
        (0, deriv (fun s => (F s).2) t) t :=
      HasDerivAt.prodMk (hasDerivAt_const t (-delta))
        (hFs.differentiableAt (by simp)).snd.hasDerivAt
    have hd : HasDerivAt F (0, deriv (fun s => (F s).2) t) t :=
      HasDerivAt.congr_of_eventuallyEq hpair heq
    intro hz
    change deriv (fun s : ℝ => (F s).2) t = 0 at hz
    have hbad : (1 : ℝ) = 0 := hinj (by
      ext <;> simp [fderiv_eq_smul_deriv, hd.deriv, hz])
    exact one_ne_zero hbad
  refine ⟨eta, heta, he0, heSmall, ?_⟩
  intro i
  have hmap0 : MapsTo (alpha i) (Ioo (-eta) eta)
      (E (finProdFinEquiv (i, (0 : Fin 2)))).target := by
    intro t ht
    exact hm0 i ⟨by linarith [ht.1, her i], ht.2.trans_le (her i)⟩
  have hmap1 : MapsTo (alpha i) (Ioo (1 - eta) (1 + eta))
      (E (finProdFinEquiv (i, (1 : Fin 2)))).target := by
    intro t ht
    exact hm1 i ⟨by linarith [ht.1, her i], by linarith [ht.2, her i]⟩
  have hs0 : ContDiffOn ℝ ∞ (b0 i) (Ioo (-eta) eta) :=
    (((hEinv (finProdFinEquiv (i, (0 : Fin 2)))).comp
      (hAlpha i).contMDiffOn hmap0).contDiffOn).snd
  have hs1 : ContDiffOn ℝ ∞ (b1 i) (Ioo (1 - eta) (1 + eta)) :=
    (((hEinv (finProdFinEquiv (i, (1 : Fin 2)))).comp
      (hAlpha i).contMDiffOn hmap1).contDiffOn).snd
  have hb0 : b0 i 0 = 0 := by
    change ((E (finProdFinEquiv (i, (0 : Fin 2)))).symm (alpha i 0)).2 = 0
    rw [(hEnds i).1, (E _).left_inv (hcenter _)]
  have hb1 : b1 i 1 = 0 := by
    change ((E (finProdFinEquiv (i, (1 : Fin 2)))).symm (alpha i 1)).2 = 0
    rw [(hEnds i).2, (E _).left_inv (hcenter _)]
  have hmem0 : (0 : ℝ) ∈ Ioo (-eta) eta := ⟨by linarith, heta⟩
  have hmem1 : (1 : ℝ) ∈ Ioo (1 - eta) (1 + eta) := ⟨by linarith, by linarith⟩
  have hd0 : HasDerivAt (b0 i) (deriv (b0 i) 0) 0 :=
    ((hs0.contDiffAt (isOpen_Ioo.mem_nhds hmem0)).differentiableAt (by simp)).hasDerivAt
  have hd1 : HasDerivAt (b1 i) (deriv (b1 i) 1) 1 :=
    ((hs1.contDiffAt (isOpen_Ioo.mem_nhds hmem1)).differentiableAt (by simp)).hasDerivAt
  have hn0 : deriv (b0 i) 0 ≠ 0 := hnonzero i _ 0 (hmap0 hmem0)
  have hn1 : deriv (b1 i) 1 ≠ 0 := hnonzero i _ 1 (hmap1 hmem1)
  have hpos0 : 0 ≤ deriv (b0 i) 0 := by
    apply ge_of_tendsto hd0.tendsto_slope_zero_right
    filter_upwards [Ioo_mem_nhdsGT heta] with s hs
    have htarget := hmap0 (show s ∈ Ioo (-eta) eta from ⟨by linarith [hs.1], hs.2⟩)
    have hbs : 0 < b0 i s :=
      not_le.mp ((hclosedAt i _ s htarget).not.mp
        (hExterior i s ⟨hs.1, by linarith [hs.2]⟩))
    simpa only [zero_add, hb0, sub_zero, smul_eq_mul] using
      mul_nonneg (inv_nonneg.mpr hs.1.le) hbs.le
  have hneg1 : deriv (b1 i) 1 ≤ 0 := by
    apply le_of_tendsto hd1.tendsto_slope_zero_right
    filter_upwards [Ioo_mem_nhdsGT heta] with s hs
    have htarget := hmap1 (show 1 + s ∈ Ioo (1 - eta) (1 + eta) from
      ⟨by linarith [hs.1], by linarith [hs.2]⟩)
    have hbs : b1 i (1 + s) ≤ 0 := (hclosedAt i _ (1 + s) htarget).mp
      (hAfter i (1 + s) ⟨by linarith [hs.1], by linarith [hs.2]⟩)
    simpa only [hb1, sub_zero, smul_eq_mul] using
      mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hs.1.le) hbs
  have hderiv0 : 0 < deriv (b0 i) 0 := lt_of_le_of_ne hpos0 (Ne.symm hn0)
  have hderiv1 : 0 < deriv (fun t => 1 - b1 i t) 1 := by
    rw [deriv_const_sub]
    exact neg_pos.mpr (lt_of_le_of_ne hneg1 hn1)
  exact ⟨hmap0, hmap1, hs0, hs1, hb0, hb1, hderiv0, hderiv1,
    fun t ht => hcoords i _ t (hmap0 ht), fun t ht => hcoords i _ t (hmap1 ht)⟩

end PoincareConjecture.M25.Topology3D
