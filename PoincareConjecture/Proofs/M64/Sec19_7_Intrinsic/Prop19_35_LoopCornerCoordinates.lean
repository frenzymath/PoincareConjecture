import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ExactCornerRegion

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Bundle Matrix

namespace PoincareConjecture

theorem m64Intrinsic_exists_loop_corner_coordinates
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T : ℝ} (hT : 0 < T)
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hind : LinearIndependent ℝ
      (![deriv gamma 0, -deriv gamma T] : Fin 2 → AnnulusCoordinates))
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T) :
    ∃ (phi : AnnulusCoordinates → ℝ × ℝ)
      (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ)) (positive : Bool),
      HasFDerivAt phi L.toContinuousLinearMap (gamma 0) ∧ phi (gamma 0) = 0 ∧
      L.symm (1, 0) = deriv gamma 0 ∧ L.symm (0, 1) = -deriv gamma T ∧
      (∀ᶠ z in 𝓝 (gamma 0), z ∈ closure U ↔
        if positive then 0 ≤ (phi z).1 ∧ 0 ≤ (phi z).2
        else (phi z).1 ≤ 0 ∨ (phi z).2 ≤ 0) := by
  obtain ⟨H, h0, hbase, hH, hHi, haxis, haxis', _, hside⟩ :=
    m64Intrinsic_exists_exact_loop_corner_region hg hT hend hinj hind hU hV hdisj hfU hfV
  have hD : H.MDifferentiable 𝓘(ℝ, ℝ × ℝ) (𝓡 2) :=
    ⟨hH.contMDiffOn.mdifferentiableOn (by simp),
      hHi.contMDiffOn.mdifferentiableOn (by simp)⟩
  let J : (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates := hD.mfderiv h0
  have hJ : J.toContinuousLinearMap = fderiv ℝ H 0 := by
    change mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) H 0 = fderiv ℝ H 0
    exact mfderiv_eq_fderiv
  have hd : HasFDerivAt H J.toContinuousLinearMap 0 := by
    rw [hJ]
    exact ((hH 0 h0).contDiffAt (H.open_source.mem_nhds h0)).differentiableAt
      (by simp) |>.hasFDerivAt
  have htarget : gamma 0 ∈ H.target := hbase ▸ H.map_source h0
  have hzero : H.symm (gamma 0) = 0 := by rw [← hbase, H.left_inv h0]
  have hdi : HasFDerivAt H.symm J.symm.toContinuousLinearMap (gamma 0) := by
    apply H.hasFDerivAt_symm htarget
    simpa only [hzero] using hd
  have hu : J (1, 0) = deriv gamma 0 := by
    have hp : HasDerivAt (fun s : ℝ => (s, (0 : ℝ))) (1, 0) 0 :=
      (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 (0 : ℝ))
    have hh := hd.comp_hasDerivAt (f := fun s : ℝ => (s, (0 : ℝ))) 0 hp
    have heq : (fun s : ℝ => H (s, 0)) = gamma := funext haxis
    change HasDerivAt (fun s : ℝ => H (s, 0)) (J (1, 0)) 0 at hh
    rw [heq] at hh
    exact hh.deriv.symm
  have hv : J (0, 1) = -deriv gamma T := by
    have hp : HasDerivAt (fun s : ℝ => ((0 : ℝ), s)) (0, 1) 0 :=
      (hasDerivAt_const 0 (0 : ℝ)).prodMk (hasDerivAt_id 0)
    have hh := hd.comp_hasDerivAt (f := fun s : ℝ => ((0 : ℝ), s)) 0 hp
    have heq : (fun s : ℝ => H (0, s)) = fun s => gamma (T - s) := funext haxis'
    change HasDerivAt (fun s : ℝ => H (0, s)) (J (0, 1)) 0 at hh
    rw [heq] at hh
    have hgamma : HasDerivAt gamma (deriv gamma T) (T - (0 : ℝ)) := by
      simpa only [sub_zero] using (hg.differentiable (by simp) T).hasDerivAt
    have hother : HasDerivAt (fun s : ℝ => gamma (T - s)) (-deriv gamma T) 0 := by
      simpa only [sub_self, zero_sub, neg_one_smul, Function.comp_def] using
        hgamma.scomp 0 ((hasDerivAt_const 0 T).sub (hasDerivAt_id 0))
    exact hh.unique hother
  obtain ⟨positive, hregion⟩ : ∃ positive : Bool, ∀ z ∈ H.target,
      z ∈ closure U ↔ if positive then 0 ≤ (H.symm z).1 ∧ 0 ≤ (H.symm z).2
        else (H.symm z).1 ≤ 0 ∨ (H.symm z).2 ≤ 0 := by
    rcases hside with hs | hs
    · refine ⟨true, fun z hz => ?_⟩
      simpa only [H.right_inv hz, if_true] using hs (H.symm z) (H.map_target hz)
    · refine ⟨false, fun z hz => ?_⟩
      simpa only [H.right_inv hz, Bool.false_eq_true, if_false] using
        hs (H.symm z) (H.map_target hz)
  refine ⟨H.symm, J.symm, positive, hdi, hzero, hu, hv, ?_⟩
  filter_upwards [H.open_target.mem_nhds htarget] with z hz
  exact hregion z hz

end PoincareConjecture
