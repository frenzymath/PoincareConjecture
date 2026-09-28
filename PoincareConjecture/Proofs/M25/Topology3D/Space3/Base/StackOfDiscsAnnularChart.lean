import PoincareConjecture.Proofs.M25.Topology3D.Space3.SphereInterpolation
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CircleRadialChart
import Mathlib.Topology.MetricSpace.Thickening











set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

local notation "P" => (ℝ × E2)
local notation "SP" => (ℝ × (ℝ × E2))


noncomputable def stackAnnularInterpolation
    (g : P → E2) (p : SP) : SP :=
  (p.1, (p.2.1, p.2.2 + Real.smoothTransition p.1 • (g p.2 - p.2.2)))


theorem stackAnnularInterpolation_invertible_derivative
    (g : P → E2) (U : Set P) (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U) (z : ℝ) (q : E2)
    (hzq : (z, q) ∈ U) (hq : ‖q‖ = 1)
    (hfixed : ∀ y : E2, ‖y‖ = 1 → g (z, y) = y)
    (hn : 0 < ⟪q, fderiv ℝ (fun y => g (z, y)) q q⟫_ℝ)
    (t : ℝ) :
    ∃ L : SP ≃L[ℝ] SP,
      HasFDerivAt (stackAnnularInterpolation g) (L : SP →L[ℝ] SP) (t, (z, q)) := by
  have hgd := (hg.contDiffAt (hU.mem_nhds hzq)).differentiableAt (by simp)
  have hinc : HasFDerivAt (fun y : E2 => (z, y))
      ((0 : E2 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E2)) q :=
    (hasFDerivAt_const z q).prodMk (hasFDerivAt_id q)
  have hf := hgd.hasFDerivAt.comp q hinc
  have htan := fun v hv => fderiv_eq_of_local_fixed_sphere
    (fun y => g (z, y)) q v hq hf.differentiableAt
      (Filter.Eventually.of_forall hfixed) hv
  obtain ⟨B, hB⟩ := fixedHyperplane_interpolation_isUnit
    (fderiv ℝ (fun y => g (z, y)) q) q hq htan hn
      ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  let D := fderiv ℝ g (z, q)
  let J : P →L[ℝ] P := (ContinuousLinearMap.fst ℝ ℝ E2).prod
    (ContinuousLinearMap.snd ℝ ℝ E2 +
      Real.smoothTransition t • (D - ContinuousLinearMap.snd ℝ ℝ E2))
  let L0 : SP →L[ℝ] SP := (ContinuousLinearMap.id ℝ ℝ).prodMap J
  have hs : HasFDerivAt (@Prod.snd ℝ P)
      (ContinuousLinearMap.snd ℝ ℝ P) (t, (z, q)) := hasFDerivAt_snd
  have ht : HasFDerivAt (@Prod.fst ℝ P)
      (ContinuousLinearMap.fst ℝ ℝ P) (t, (z, q)) := hasFDerivAt_fst
  have hsmooth : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hstep := (hsmooth.differentiable (by simp) t).hasFDerivAt
  have hd : HasFDerivAt (stackAnnularInterpolation g) L0 (t, (z, q)) := by
    have h := ht.prodMk (hs.fst.prodMk (hs.snd.fun_add
      ((hstep.comp (t, (z, q)) ht).fun_smul
        ((hgd.hasFDerivAt.comp (t, (z, q)) hs).fun_sub hs.snd))))
    apply h.congr_fderiv
    apply ContinuousLinearMap.ext
    intro v
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · change v.2.2 + (Real.smoothTransition t • (D v.2 - v.2.2) +
            (fderiv ℝ Real.smoothTransition t v.1) • (g (z, q) - q)) =
          v.2.2 + Real.smoothTransition t • (D v.2 - v.2.2)
        rw [hfixed q hq, sub_self, smul_zero, add_zero]
  have hi : Function.Injective L0 := by
    apply (injective_iff_map_eq_zero _).mpr
    intro v hv
    have htime : v.1 = 0 := congrArg Prod.fst hv
    have hheight : v.2.1 = 0 := congrArg (fun p : SP => p.2.1) hv
    have hpair : v.2 = (0, v.2.2) := Prod.ext hheight rfl
    have hslice : D (0, v.2.2) = fderiv ℝ (fun y => g (z, y)) q v.2.2 := by
      change D (0, v.2.2) = (fderiv ℝ (g ∘ Prod.mk z) q) v.2.2
      rw [hf.fderiv]
      rfl
    have hplane := congrArg (fun p : SP => p.2.2) hv
    change v.2.2 + Real.smoothTransition t • (D v.2 - v.2.2) = 0 at hplane
    rw [hpair, hslice] at hplane
    have hBzero : (B : E2 →L[ℝ] E2) v.2.2 = 0 := by
      rw [hB]
      change (1 - Real.smoothTransition t) • v.2.2 +
        Real.smoothTransition t • fderiv ℝ (fun y => g (z, y)) q v.2.2 = 0
      calc
        _ = v.2.2 + Real.smoothTransition t •
            (fderiv ℝ (fun y => g (z, y)) q v.2.2 - v.2.2) := by module
        _ = 0 := hplane
    have hx : v.2.2 = 0 := (ContinuousLinearEquiv.ofUnit B).injective (by
      change (B : E2 →L[ℝ] E2) v.2.2 = (B : E2 →L[ℝ] E2) 0
      simpa only [map_zero] using hBzero)
    exact Prod.ext htime (Prod.ext hheight hx)
  have hu : IsUnit L0 := ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi⟩
  obtain ⟨V, hV⟩ := hu
  refine ⟨ContinuousLinearEquiv.ofUnit V, ?_⟩
  change HasFDerivAt (stackAnnularInterpolation g) (V : SP →L[ℝ] SP) (t, (z, q))
  rw [hV]
  exact hd


theorem exists_stackAnnularInterpolationChart
    (g : P → E2) (U : Set P) (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U) (A a b B : ℝ)
    (hAa : A < a) (hab : a < b) (hbB : b < B)
    (hCU : Icc A B ×ˢ sphere (0 : E2) 1 ⊆ U)
    (hfixed : ∀ z ∈ Icc A B, ∀ q ∈ sphere (0 : E2) 1, g (z, q) = q)
    (hn : ∀ z ∈ Icc A B, ∀ q ∈ sphere (0 : E2) 1,
      0 < ⟪q, fderiv ℝ (fun y => g (z, y)) q q⟫_ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 4 ∧
      ∃ e : OpenPartialHomeomorph SP SP,
        (e : SP → SP) = stackAnnularInterpolation g ∧
        e.source = Ioo (-2 : ℝ) 3 ×ˢ
          (Ioo A B ×ˢ {x : E2 | |‖x‖ - 1| < 2 * δ}) ∧
        ContDiffOn ℝ ∞ e e.source ∧
        ContDiffOn ℝ ∞ e.symm e.target ∧
        (Ioo A B ×ˢ {x : E2 | |‖x‖ - 1| < 2 * δ}) ⊆ U ∧
        Icc (-1 : ℝ) 2 ×ˢ
          (Icc a b ×ˢ {x : E2 | |‖x‖ - 1| ≤ δ}) ⊆ e.source := by
  let K : Set SP := Icc (-3 : ℝ) 4 ×ˢ (Icc A B ×ˢ sphere (0 : E2) 1)
  have hK : IsCompact K := isCompact_Icc.prod
    (isCompact_Icc.prod (isCompact_sphere (0 : E2) 1))
  have hF : ContDiffOn ℝ ∞ (stackAnnularInterpolation g) (univ ×ˢ U) :=
    contDiff_fst.contDiffOn.prodMk (contDiff_snd.fst.contDiffOn.prodMk
      (contDiff_snd.snd.contDiffOn.add
        ((Real.smoothTransition.contDiff.comp contDiff_fst).contDiffOn.smul
          ((hg.comp contDiff_snd.contDiffOn (fun _ hp => hp.2)).sub
            contDiff_snd.snd.contDiffOn))))
  have hfix (p : SP) (hp : p ∈ K) : stackAnnularInterpolation g p = p := by
    rcases p with ⟨t, z, q⟩
    simp only [stackAnnularInterpolation, hfixed z hp.2.1 q hp.2.2,
      sub_self, smul_zero, add_zero]
  obtain ⟨e0, he0, hKe, heU, hsm, hsi⟩ := exists_smoothChart_near_compact
    (stackAnnularInterpolation g) hK (isOpen_univ.prod hU)
    (fun _ hp => ⟨mem_univ _, hCU hp.2⟩) hF
    (fun p hp q hq hpq => by simpa only [hfix p hp, hfix q hq] using hpq)
    (by
      intro p hp
      exact stackAnnularInterpolation_invertible_derivative g U hU hg p.2.1 p.2.2
        (hCU hp.2) (mem_sphere_zero_iff_norm.mp hp.2.2)
        (fun y hy => hfixed p.2.1 hp.2.1 y (mem_sphere_zero_iff_norm.mpr hy))
        (hn p.2.1 hp.2.1 p.2.2 hp.2.2) p.1)
  obtain ⟨d, hd, hde⟩ := hK.exists_thickening_subset_open e0.open_source hKe
  obtain ⟨δ, hδ, hδm⟩ := exists_between
    (show (0 : ℝ) < min (1 / 4) (d / 3) from
      lt_min (by norm_num) (div_pos hd (by norm_num)))
  have hδquarter : δ < 1 / 4 := (lt_min_iff.mp hδm).1
  have hδd : 2 * δ < d := by linarith only [(lt_min_iff.mp hδm).2, hd]
  have hdist (x : E2) : dist x (circleDirection x : E2) = |‖x‖ - 1| := by
    rw [dist_eq_norm]
    have hsub : x - (circleDirection x : E2) =
        (‖x‖ - 1) • (circleDirection x : E2) := by
      rw [sub_smul, one_smul, circleDirection_norm_smul]
    rw [hsub, norm_smul, Real.norm_eq_abs, norm_eq_of_mem_sphere, mul_one]
  let V : Set SP := Ioo (-2 : ℝ) 3 ×ˢ
    (Ioo A B ×ˢ {x : E2 | |‖x‖ - 1| < 2 * δ})
  have hVo : IsOpen V := isOpen_Ioo.prod (isOpen_Ioo.prod
    (isOpen_lt (continuous_norm.sub continuous_const).abs continuous_const))
  have hVe : V ⊆ e0.source := by
    rintro ⟨t, z, x⟩ ⟨ht, hz, hx⟩
    apply hde
    apply mem_thickening_iff.mpr
    refine ⟨(t, (z, (circleDirection x : E2))), ?_, ?_⟩
    · exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩,
        ⟨hz.1.le, hz.2.le⟩, (circleDirection x).2⟩
    · simpa only [dist_prod_same_left, hdist] using hx.trans hδd
  let e := e0.restrOpen V hVo
  have hse : e.source = V := inter_eq_right.mpr hVe
  refine ⟨δ, hδ, hδquarter, e, he0, hse, hsm.mono inter_subset_left,
    hsi.mono (fun _ hp => hp.1), ?_, ?_⟩
  · intro p hp
    exact (heU (hVe (show (0, p) ∈ V from ⟨by norm_num, hp⟩))).2
  · rintro ⟨t, z, x⟩ ⟨ht, hz, hx⟩
    change |‖x‖ - 1| ≤ δ at hx
    have hheightBand : Icc a b ⊆ Ioo A B :=
      (Icc_subset_Ioo_iff hab.le).mpr ⟨hAa, hbB⟩
    rw [hse]
    exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩,
      hheightBand hz, by
        change |‖x‖ - 1| < 2 * δ
        linarith only [hx, hδ]⟩

end PoincareConjecture.M25.Topology3D
