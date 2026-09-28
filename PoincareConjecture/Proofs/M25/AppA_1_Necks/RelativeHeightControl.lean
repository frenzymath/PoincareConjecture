import PoincareConjecture.Proofs.M25.AppA_1_Necks.TransitionHeight
import PoincareConjecture.Proofs.M25.AppA_1_Necks.SharpDepth
import PoincareConjecture.Proofs.M25.Mathlib.PlateauMeanValue
import Mathlib.Topology.Order.IntermediateValue










set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture



theorem EpsilonNeck.exists_relative_height_lower_control :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N R : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → R.epsilon = N.epsilon →
        let L := N.epsilon⁻¹
        ∀ (X : Set M), R.carrier ⊆ X →
        ∀ (F : M → ℝ), ContinuousOn F X →
          (∀ x ∈ N.carrier, F x = (N.coordinate_inverse x).2) →
          (∀ x ∈ X, x ∉ N.carrier → F x = -L ∨ F x = L) →
          F R.center = L →
          ∀ x ∈ R.carrier, -L / 5 < F x := by
  let B0 : ℝ := Real.sqrt 2 * (Real.pi + 1)
  have hB0 : 0 < B0 := by dsimp only [B0]; positivity
  have hden : 0 < 10000 * (B0 + 1) := by positivity
  obtain ⟨es, hspos, hscap, hscale⟩ :=
    EpsilonNeck.exists_intersecting_scale_control.{u} (α := (1 / 1000 : ℝ))
      (by norm_num)
  obtain ⟨ea, hapos, _, haxis⟩ :=
    EpsilonNeck.exists_intersecting_axial_derivative_control.{u}
      (η := (1 / 1000 : ℝ)) (by norm_num)
  refine ⟨min es (min ea (min (1 / 10000) (1 / (10000 * (B0 + 1))))),
    lt_min hspos (lt_min hapos (lt_min (by norm_num) (div_pos zero_lt_one hden))),
    (min_le_left _ _).trans hscap, ?_⟩
  intro M _ _ _ _ _ _ g N R hsmall heR
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  let L : ℝ := N.epsilon⁻¹
  dsimp only
  intro X hRX F hF hFin hFout hcenter
  change F R.center = L at hcenter
  change ∀ x ∈ X, x ∉ N.carrier → F x = -L ∨ F x = L at hFout
  change ∀ x ∈ R.carrier, -L / 5 < F x
  rcases le_min_iff.mp hsmall with ⟨hes, hrest⟩
  rcases le_min_iff.mp hrest with ⟨hea, hrest⟩
  rcases le_min_iff.mp hrest with ⟨henumeric, hbudget⟩
  have hL : 0 < L := inv_pos.mpr N.epsilon_pos
  have hNscale : 0 < N.scale := N.scale_pos
  have hB0e : B0 * N.epsilon ≤ 1 / 10000 := by
    have h := (le_div_iff₀ hden).mp hbudget
    nlinarith only [h, N.epsilon_pos]
  have hB0L : B0 ≤ L / 10000 := by
    calc
      B0 ≤ (1 / 10000) / N.epsilon := (le_div_iff₀ N.epsilon_pos).mpr hB0e
      _ = L / 10000 := by dsimp only [L]; ring
  have hsqlo : (999 : ℝ) / 1000 ≤ Real.sqrt (1 - N.epsilon) :=
    Real.le_sqrt_of_sq_le (by nlinarith only [henumeric])
  have hsqhi : Real.sqrt (1 + N.epsilon) ≤ (1001 : ℝ) / 1000 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith only [henumeric]⟩
  have hzero : (0 : ℝ) ∈ Ioo (-R.epsilon⁻¹) R.epsilon⁻¹ := by
    rw [heR]
    exact ⟨neg_lt_zero.mpr hL, hL⟩
  have hcR := (R.mem_central_sphere_iff R.center).mp R.center_on_central_sphere
  have hyN : R.center ∉ N.carrier := by
    intro hy
    have h := (N.coordinate_inverse_mem R.center hy).2.2
    rw [← hFin R.center hy, hcenter] at h
    exact lt_irrefl L h
  have hbounds (x : M) (hx : x ∈ X) : F x ∈ Icc (-L) L := by
    by_cases hxN : x ∈ N.carrier
    · rw [hFin x hxN]
      exact Ioo_subset_Icc_self (N.coordinate_inverse_mem x hxN).2
    · rcases hFout x hx hxN with h | h <;> rw [h] <;>
        constructor <;> linarith only [hL]
  have hmem (x : M) (hx : x ∈ X) (hlo : -L < F x) (hhi : F x < L) :
      x ∈ N.carrier := by
    by_contra hxN
    rcases hFout x hx hxN with h | h
    · exact hlo.ne h.symm
    · exact hhi.ne h
  let J : UnitTwoSphere → ℝ := fun q => F (R.coordinate_map (q, 0))
  have hJ : Continuous J := by
    apply hF.comp_continuous
      (R.coordinate_map_smooth.continuousOn.comp_continuous
        (continuous_id.prodMk continuous_const) (fun q => ⟨mem_univ q, hzero⟩))
    intro q
    exact hRX (R.coordinate_map_mem ⟨mem_univ q, hzero⟩)
  let q0 := (R.coordinate_inverse R.center).1
  have hq0 : R.coordinate_map (q0, 0) = R.center := by
    change R.coordinate_map ((R.coordinate_inverse R.center).1, 0) = R.center
    rw [← hcR.2]
    exact R.coordinate_map_inverse hcR.1
  have hJ0 : J q0 = L := by simpa only [J, hq0] using hcenter
  have hsphere (q : UnitTwoSphere) : 9 * L / 10 < J q := by
    by_contra hbad
    obtain ⟨p, hp⟩ := intermediate_value_univ₂ hJ continuous_const
      (le_of_not_gt hbad)
      (show (9 * L / 10 : ℝ) ≤ J q0 by rw [hJ0]; linarith only [hL])
    let z := R.coordinate_map (p, 0)
    change F z = 9 * L / 10 at hp
    have hzR : z ∈ R.carrier := R.coordinate_map_mem ⟨mem_univ _, hzero⟩
    have hzN : z ∈ N.carrier := hmem z (hRX hzR)
      (by rw [hp]; linarith only [hL]) (by rw [hp]; linarith only [hL])
    have hzheight : (R.coordinate_inverse z).2 = 0 :=
      congrArg Prod.snd (R.coordinate_inverse_map (p, 0) hzero)
    have hzdepth : N.axialDepth z = L / 10 := by
      rw [EpsilonNeck.axialDepth, if_pos hzN, ← hFin z hzN, hp,
        abs_of_pos (by positivity : 0 < 9 * L / 10)]
      dsimp only [L]
      ring
    have hydepth : N.axialDepth R.center = 0 := by
      simp only [EpsilonNeck.axialDepth, if_neg hyN]
    have hd := N.axialDepth_edist_le z R.center
    rw [hzdepth, hydepth, sub_zero, abs_of_pos (by positivity : 0 < L / 10)] at hd
    have hu := R.edist_le_axial_add hzR hcR.1
    rw [hcR.2, hzheight, sub_self, abs_zero, zero_add, heR] at hu
    change g.edist z R.center ≤
      ENNReal.ofReal (R.scale * Real.sqrt (1 + N.epsilon) * B0) at hu
    have hratio := (hscale N R hes (by rw [heR]; exact hes) ⟨z, hzN, hzR⟩).2
    have hr : R.scale ≤ (1001 / 1000 : ℝ) * N.scale := by
      apply (div_le_iff₀ N.scale_pos).mp
      linarith only [(abs_lt.mp hratio).2]
    have hcoeff : R.scale * Real.sqrt (1 + N.epsilon) ≤
        (101 / 100 : ℝ) * N.scale := by
      calc
        _ ≤ ((1001 / 1000 : ℝ) * N.scale) * (1001 / 1000) :=
          mul_le_mul hr hsqhi (Real.sqrt_nonneg _) (by positivity)
        _ ≤ _ := by nlinarith only [N.scale_pos]
    have hreal := (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (mul_nonneg R.scale_pos.le (Real.sqrt_nonneg _)) hB0.le)).mp
        (hd.trans hu)
    have hlo := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsqlo N.scale_pos.le) (by positivity : 0 ≤ L / 10)
    have hupper := (mul_le_mul_of_nonneg_right hcoeff hB0.le).trans
      (mul_le_mul_of_nonneg_left hB0L (by positivity : 0 ≤ (101 / 100 : ℝ) * N.scale))
    nlinarith only [hreal, hlo, hupper, mul_pos N.scale_pos hL]
  have hmap (q : UnitTwoSphere) :
      ContinuousOn (fun t : ℝ => R.coordinate_map (q, t)) (Ioo (-L) L) := by
    apply R.coordinate_map_smooth.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
    intro t ht
    exact ⟨mem_univ _, by simpa only [heR, L, id_eq] using ht⟩
  have hline (q : UnitTwoSphere) :
      ContinuousOn (fun t : ℝ => F (R.coordinate_map (q, t))) (Ioo (-L) L) := by
    apply hF.comp (hmap q)
    intro t ht
    exact hRX (R.coordinate_map_mem ⟨mem_univ _, by simpa only [heR, L] using ht⟩)
  have hderivative (q : UnitTwoSphere) (t : ℝ) (ht : t ∈ Ioo (-L) L)
      (hlo : -L < F (R.coordinate_map (q, t)))
      (hhi : F (R.coordinate_map (q, t)) < L) :
      DifferentiableAt ℝ (fun s => F (R.coordinate_map (q, s))) t ∧
        |deriv (fun s => F (R.coordinate_map (q, s))) t| ≤ (101 / 100 : ℝ) := by
    have hz : (q, t) ∈ R.cylinderDomain :=
      ⟨mem_univ _, by simpa only [heR, L] using ht⟩
    have hxR := R.coordinate_map_mem hz
    have hxN := hmem _ (hRX hxR) hlo hhi
    have hm := R.coordinate_map_smooth.contMDiffAt (R.cylinderDomain_open.mem_nhds hz)
    have hi := N.coordinate_inverse_smooth.contMDiffAt (N.carrier_open.mem_nhds hxN)
    have hp : ContMDiffAt 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
        (fun s : ℝ => (q, s)) t := contMDiffAt_const.prodMk contMDiffAt_id
    have hd : DifferentiableAt ℝ
        (fun s => (N.coordinate_inverse (R.coordinate_map (q, s))).2) t :=
      mdifferentiableAt_iff_differentiableAt.mp
        ((contMDiffAt_snd.comp t (hi.comp t (hm.comp t hp))).mdifferentiableAt (by simp))
    have hratio := (hscale N R hes (by rw [heR]; exact hes)
      ⟨R.coordinate_map (q, t), hxN, hxR⟩).2
    have hr : R.scale / N.scale ≤ 2 := by linarith only [(abs_lt.mp hratio).2]
    obtain ⟨sigma, hsigma, hcross⟩ := haxis R N (by rw [heR]; exact hea) hea
      (R.coordinate_map (q, t)) hxR hxN
    have he := R.transition_height_axial_error N hz hxN (τ := (1 / 1000 : ℝ))
      hsigma (by norm_num) hratio.le hr (by simpa only [mul_assoc] using hcross.le)
    have hsigmaAbs : |sigma| = 1 := by
      rcases hsigma with rfl | rfl <;> norm_num
    have htriangle := abs_add_le
      (deriv (fun s => (N.coordinate_inverse (R.coordinate_map (q, s))).2) t - sigma) sigma
    rw [sub_add_cancel, hsigmaAbs] at htriangle
    have hnear := ((hmap q).continuousAt (isOpen_Ioo.mem_nhds ht)).eventually
      (N.carrier_open.mem_nhds hxN)
    have heq : Filter.EventuallyEq (nhds t)
        (fun s => F (R.coordinate_map (q, s)))
        (fun s => (N.coordinate_inverse (R.coordinate_map (q, s))).2) :=
      hnear.mono (fun s hs => hFin _ hs)
    refine ⟨hd.congr_of_eventuallyEq heq, ?_⟩
    rw [heq.deriv_eq]
    linarith only [he, htriangle]
  intro x hxR
  let q := (R.coordinate_inverse x).1
  let s := (R.coordinate_inverse x).2
  have hs : s ∈ Ioo (-L) L := by
    simpa only [heR, L] using (R.coordinate_inverse_mem x hxR).2
  have hsabs : |s| < L := abs_lt.mpr hs
  have hx : R.coordinate_map (q, s) = x := R.coordinate_map_inverse hxR
  by_contra hbad
  let h : ℝ → ℝ := fun t => F (R.coordinate_map (q, t * s))
  have hstrip (t : ℝ) (ht : t ∈ Icc 0 1) : t * s ∈ Ioo (-L) L := by
    apply abs_lt.mp
    calc
      |t * s| = t * |s| := by rw [abs_mul, abs_of_nonneg ht.1]
      _ ≤ 1 * |s| := mul_le_mul_of_nonneg_right ht.2 (abs_nonneg s)
      _ < L := by simpa only [one_mul] using hsabs
  have hh : ContinuousOn h (Icc 0 1) :=
    (hline q).comp (continuous_id.mul continuous_const).continuousOn hstrip
  have hh0 : 9 * L / 10 < h 0 := by simpa only [h, zero_mul, J] using hsphere q
  have hh1 : h 1 ≤ -L / 5 := by
    simpa only [h, one_mul, hx] using le_of_not_gt hbad
  let S : Set ℝ := Icc 0 1 ∩ h ⁻¹' {-L / 5}
  have hSclosed : IsClosed S := hh.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hScompact : IsCompact S :=
    isCompact_Icc.of_isClosed_subset hSclosed inter_subset_left
  have hS : S.Nonempty := by
    obtain ⟨t, ht, hvalue⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hh
      ⟨hh1, by linarith only [hh0, hL]⟩
    exact ⟨t, ht, hvalue⟩
  obtain ⟨tau, htau⟩ := hScompact.exists_isLeast hS
  have htau01 : tau ∈ Icc 0 1 := htau.1.1
  have htauValue : h tau = -L / 5 := htau.1.2
  have htaupos : 0 < tau := by
    apply lt_of_le_of_ne htau01.1
    intro heq
    rw [← heq] at htauValue
    linarith only [hh0, htauValue, hL]
  have hprefix (t : ℝ) (ht : t ∈ Icc 0 tau) : -L / 5 ≤ h t := by
    by_contra hlow
    have hlowlt : h t < -L / 5 := lt_of_not_ge hlow
    have htlt : t < tau := lt_of_le_of_ne ht.2 (by
      intro heq
      rw [heq, htauValue] at hlowlt
      exact lt_irrefl _ hlowlt)
    have hsub : Icc 0 t ⊆ Icc 0 1 := Icc_subset_Icc le_rfl (ht.2.trans htau01.2)
    obtain ⟨v, hv, hvalue⟩ := intermediate_value_Icc' ht.1 (hh.mono hsub)
      ⟨hlowlt.le, by linarith only [hh0, hL]⟩
    have hvS : v ∈ S := ⟨hsub hv, hvalue⟩
    exact (not_le_of_gt (hv.2.trans_lt htlt)) (htau.2 hvS)
  have hbound : |h tau - h 0| ≤ ((101 / 100 : ℝ) * |s|) * |tau - 0| := by
    apply Real.abs_sub_le_mul_abs_sub_of_deriv_le_below (c := L)
    · rw [uIcc_of_le htaupos.le]
      exact hh.mono (Icc_subset_Icc le_rfl htau01.2)
    · positivity
    · intro t ht
      rw [uIcc_of_le htaupos.le] at ht
      exact (hbounds _ (hRX (R.coordinate_map_mem
        ⟨mem_univ _, by simpa only [heR, L] using
          (hstrip t ⟨ht.1, ht.2.trans htau01.2⟩)⟩))).2
    · intro t ht hbelow
      rw [uIoo_of_le htaupos.le] at ht
      have ht01 : t ∈ Icc 0 1 := ⟨ht.1.le, ht.2.le.trans htau01.2⟩
      have hd := hderivative q (t * s) (hstrip t ht01)
        (by have hp := hprefix t ⟨ht.1.le, ht.2.le⟩; linarith only [hp, hL]) hbelow
      have hchain : HasDerivAt h
          (deriv (fun r => F (R.coordinate_map (q, r))) (t * s) * s) t := by
        simpa only [h, Function.comp_def, id_eq, one_mul] using
          hd.1.hasDerivAt.comp t ((hasDerivAt_id t).mul_const s)
      refine ⟨hchain.differentiableAt, ?_⟩
      rw [hchain.deriv, abs_mul]
      exact mul_le_mul_of_nonneg_right hd.2 (abs_nonneg s)
  have hstrict : |h tau - h 0| < (101 / 100 : ℝ) * L := by
    calc
      _ ≤ ((101 / 100 : ℝ) * |s|) * tau := by
        simpa only [sub_zero, abs_of_pos htaupos] using hbound
      _ ≤ ((101 / 100 : ℝ) * |s|) * 1 :=
        mul_le_mul_of_nonneg_left htau01.2 (by positivity)
      _ < (101 / 100 : ℝ) * L := by
        simpa only [mul_one] using mul_lt_mul_of_pos_left hsabs (by norm_num :
          (0 : ℝ) < 101 / 100)
  have hlarge : (11 / 10 : ℝ) * L < |h tau - h 0| := by
    rw [htauValue, abs_of_neg (by linarith only [hh0, hL] : -L / 5 - h 0 < 0)]
    linarith only [hh0]
  linarith only [hstrict, hlarge, hL]

end PoincareConjecture
