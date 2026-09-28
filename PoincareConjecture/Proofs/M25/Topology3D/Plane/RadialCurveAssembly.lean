import PoincareConjecture.Proofs.M25.Topology3D.Plane.PeriodicFiber
import PoincareConjecture.Proofs.M25.Topology3D.Plane.PeriodicCircle
import PoincareConjecture.Proofs.M25.Topology3D.Plane.CurveFamilyTransport
import PoincareConjecture.Proofs.M25.Topology3D.Plane.RadialCalculus
import Mathlib.Topology.Order.MonotoneContinuity

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

private theorem periodic_ne_of_short_gap {F : Type*} {γ : ℝ → F} {T : ℝ}
    (hT : 0 < T) (hper : Periodic γ T) (hinj : InjOn γ (Ico 0 T))
    {s t : ℝ} (hst : s < t) (hts : t < s + T) : γ s ≠ γ t := by
  intro heq
  let k : ℤ := ⌊s / T⌋
  let u := s - (k : ℝ) * T
  let v := t - (k : ℝ) * T
  have hlo : (k : ℝ) * T ≤ s := (le_div_iff₀ hT).mp (Int.floor_le _)
  have hhi : s < ((k : ℝ) + 1) * T := (div_lt_iff₀ hT).mp (Int.lt_floor_add_one _)
  have hu0 : 0 ≤ u := by dsimp [u]; linarith
  have huT : u < T := by dsimp [u]; nlinarith
  have huv : u < v := by dsimp [u, v]; linarith
  have hvu : v < u + T := by dsimp [u, v]; linarith
  have hsame : γ u = γ v := by
    rw [show γ u = γ s from hper.sub_int_mul_eq k,
      show γ v = γ t from hper.sub_int_mul_eq k]
    exact heq
  by_cases hvT : v < T
  · exact (ne_of_lt huv) (hinj ⟨hu0, huT⟩ ⟨by linarith, hvT⟩ hsame)
  · have hsame' : γ u = γ (v - T) := hsame.trans (hper.sub_eq v).symm
    have huv' := hinj ⟨hu0, huT⟩ ⟨by linarith, by linarith⟩ hsame'
    linarith

theorem radial_circle_lift_add_period
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : ℂ ≃ₗᵢ[ℝ] E) {T : ℝ} (hT : 0 < T)
    (B r : ℝ → ℝ) (hB : Continuous B) (hmono : StrictMono B)
    (hr : Continuous r) (hrper : Periodic r T)
    (hphase : Periodic (fun s => sphereCircleParameter e (B s)) T)
    (hinj : InjOn (fun s => r s • (sphereCircleParameter e (B s) : E)) (Ico 0 T)) :
    (∀ s, B (s + T) = B s + 2 * Real.pi) ∧
      InjOn (fun s => sphereCircleParameter e (B s)) (Ico 0 T) := by
  have hτ : 0 < 2 * Real.pi := by positivity
  have hphase' (s : ℝ) : Circle.exp (B (s + T)) = Circle.exp (B s) := by
    apply Subtype.ext
    apply e.injective
    exact congrArg Subtype.val (hphase s)
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp (by simpa only [zero_add] using hphase' 0)
  let d : ℝ := (m : ℝ) * (2 * Real.pi)
  have hd : 0 < d := by
    have hh := hmono hT
    change 0 < (m : ℝ) * (2 * Real.pi)
    linarith
  have hmpos : (0 : ℤ) < m := by
    have : (0 : ℝ) < m := (mul_pos_iff_of_pos_right hτ).mp hd
    exact_mod_cast this
  have htrans (s : ℝ) : B (s + T) = B s + d := by
    have heq : Circle.exp ∘ (fun s => B (s + T)) =
        Circle.exp ∘ (fun s => B s + d) := by
      funext s
      exact (hphase' s).trans (Circle.exp_eq_exp.mpr ⟨m, rfl⟩).symm
    have hh := Circle.isCoveringMap_exp.eq_of_comp_eq
      (hB.comp (continuous_id.add continuous_const))
      (hB.add continuous_const) heq 0 (by
        change B (0 + T) = B 0 + d
        simpa only [zero_add] using hm)
    exact congrFun hh s
  have hsurj : Surjective B := by
    have hf : Continuous (fun s => (T / d) * B s) := continuous_const.mul hB
    have hp (s : ℝ) : (T / d) * B (s + T) = (T / d) * B s + T := by
      rw [htrans, mul_add, div_mul_cancel₀ _ hd.ne']
    intro y
    obtain ⟨x, hx⟩ := surjective_of_add_period hT hf hp ((T / d) * y)
    exact ⟨x, mul_left_cancel₀ (div_pos hT hd).ne' hx⟩
  let D : ℝ ≃o ℝ := hmono.orderIsoOfSurjective B hsurj
  let J : ℝ → ℝ := D.symm
  have hBJ (u : ℝ) : B (J u) = u := D.apply_symm_apply u
  have hJ : Continuous J := D.symm.toHomeomorph.continuous
  have hJtrans (u : ℝ) : J (u + d) = J u + T := by
    apply hmono.injective
    rw [hBJ, htrans, hBJ]
  let R : ℝ → ℝ := fun u => r (J u)
  have hR : Continuous R := hr.comp hJ
  have hRper : Periodic R d := fun u => by
    dsimp only [R]
    rw [hJtrans, hrper]
  have hγper : Periodic (fun s => r s • (sphereCircleParameter e (B s) : E)) T := by
    intro s
    change r (s + T) • (sphereCircleParameter e (B (s + T)) : E) =
      r s • (sphereCircleParameter e (B s) : E)
    have hh : sphereCircleParameter e (B (s + T)) = sphereCircleParameter e (B s) := hphase s
    rw [hrper s, hh]
  have hmone : m = 1 := by
    by_contra hmne
    have hmgt : (1 : ℝ) < m := by exact_mod_cast (show (1 : ℤ) < m by omega)
    have hτd : 2 * Real.pi < d := by dsimp only [d]; nlinarith
    have hneq (u : ℝ) : R (u + 2 * Real.pi) ≠ R u := by
      intro heq
      have hjlt : J u < J (u + 2 * Real.pi) := hmono.lt_iff_lt.mp (by
        rw [hBJ, hBJ]
        linarith)
      have hjT : J (u + 2 * Real.pi) < J u + T := hmono.lt_iff_lt.mp (by
        rw [hBJ, htrans, hBJ]
        linarith)
      apply periodic_ne_of_short_gap hT hγper hinj hjlt hjT
      change R u • (sphereCircleParameter e (B (J u)) : E) =
        R (u + 2 * Real.pi) • (sphereCircleParameter e (B (J (u + 2 * Real.pi))) : E)
      rw [hBJ, hBJ, periodic_sphereCircleParameter e, heq]
    have hsign : (∀ u, R u < R (u + 2 * Real.pi)) ∨
        ∀ u, R (u + 2 * Real.pi) < R u := by
      let f : ℝ → ℝ := fun u => R (u + 2 * Real.pi) - R u
      have hf : Continuous f := (hR.comp (continuous_id.add continuous_const)).sub hR
      have hfne (u : ℝ) : f u ≠ 0 := sub_ne_zero.mpr (hneq u)
      rcases lt_or_gt_of_ne (hfne 0) with hneg | hpos
      · right
        intro u
        by_contra hu
        obtain ⟨v, hv⟩ := intermediate_value_univ 0 u hf
          ⟨hneg.le, sub_nonneg.mpr (le_of_not_gt hu)⟩
        exact hfne v hv
      · left
        intro u
        by_contra hu
        obtain ⟨v, hv⟩ := intermediate_value_univ u 0 hf
          ⟨sub_nonpos.mpr (le_of_not_gt hu), hpos.le⟩
        exact hfne v hv
    have hcycle (f : ℝ → ℝ) (hf : ∀ u, f u < f (u + 2 * Real.pi))
        (hp : Periodic f d) : False := by
      have hn (j : ℕ) : f 0 < f (((j : ℝ) + 1) * (2 * Real.pi)) := by
        induction j with
        | zero => simpa only [Nat.cast_zero, zero_add, one_mul] using hf 0
        | succ j ih =>
          have hh := hf (((j : ℝ) + 1) * (2 * Real.pi))
          have he : (((j + 1 : ℕ) : ℝ) + 1) * (2 * Real.pi) =
              ((j : ℝ) + 1) * (2 * Real.pi) + 2 * Real.pi := by
            push_cast
            ring
          rw [he]
          exact ih.trans hh
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero
        (show m.toNat ≠ 0 by omega)
      have hjm : (j : ℝ) + 1 = m := by
        have hcast : ((m.toNat : ℕ) : ℝ) = m := by
          exact_mod_cast Int.toNat_of_nonneg hmpos.le
        rw [hj, Nat.cast_succ] at hcast
        exact hcast
      have hh := hn j
      rw [hjm] at hh
      change f 0 < f d at hh
      rw [hp.eq] at hh
      exact (lt_irrefl _) hh
    rcases hsign with hpos | hneg
    · exact hcycle R hpos hRper
    · exact hcycle (fun u => -R u) (fun u => neg_lt_neg (hneg u))
        (fun u => congrArg Neg.neg (hRper u))
  have htrans' (s : ℝ) : B (s + T) = B s + 2 * Real.pi := by
    simpa only [d, hmone, Int.cast_one, one_mul] using htrans s
  refine ⟨htrans', ?_⟩
  intro s hs t ht heq
  have hBT : B T = B 0 + 2 * Real.pi := by simpa only [zero_add] using htrans' 0
  have hsB : B s ∈ Ico (B 0) (B 0 + 2 * Real.pi) :=
    ⟨hmono.monotone hs.1, hBT ▸ hmono hs.2⟩
  have htB : B t ∈ Ico (B 0) (B 0 + 2 * Real.pi) :=
    ⟨hmono.monotone ht.1, hBT ▸ hmono ht.2⟩
  exact hmono.injective (injOn_sphereCircleParameter_Ico e (by linarith) hsB htB heq)

theorem exists_radial_curve_ambient_straightening
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)]
    (e : ℂ ≃ₗᵢ[ℝ] E) (o : Orientation ℝ E (Fin 2)) (q0 : sphere (0 : E) 1)
    {T : ℝ} (hT : 0 < T) (B r : ℝ → ℝ)
    (hB : ContDiff ℝ ∞ B) (hr : ContDiff ℝ ∞ r)
    (hBpos : ∀ s, 0 < deriv B s) (hrpos : ∀ s, 0 < r s)
    (hrper : Periodic r T)
    (hphase : Periodic (fun s => sphereCircleParameter e (B s)) T)
    (hinj : InjOn (fun s => r s • (sphereCircleParameter e (B s) : E)) (Ico 0 T)) :
    ∃ D : E ≃ₘ[ℝ] E,
      D '' range (fun s => r s • (sphereCircleParameter e (B s) : E)) = sphere 0 1 := by
  obtain ⟨htrans, hPinj⟩ := radial_circle_lift_add_period e hT B r hB.continuous
    (strictMono_of_deriv_pos hBpos) hr.continuous hrper hphase hinj
  let P : ℝ → E := fun s => (sphereCircleParameter e (B s) : E)
  have hP : ContDiff ℝ ∞ P :=
    ((contMDiff_coe_sphere (E := E) (n := 1) (m := ∞)).comp
      ((contMDiff_sphereCircleParameter e).comp hB.contMDiff)).contDiff
  have hPd (s : ℝ) : HasDerivAt P
      (deriv B s • e (Complex.I * (Circle.exp (B s) : ℂ))) s :=
    (hasDerivAt_sphereCircleParameter_coe e (B s)).scomp s
      ((hB.differentiable (by simp) s).hasDerivAt)
  have hPne (s : ℝ) : deriv P s ≠ 0 := by
    rw [(hPd s).deriv]
    apply smul_ne_zero (hBpos s).ne'
    intro hz
    have hn : ‖e (Complex.I * (Circle.exp (B s) : ℂ))‖ = 1 := by
      rw [e.norm_map, norm_mul, Complex.norm_I, Circle.norm_coe, mul_one]
    rw [hz, norm_zero] at hn
    norm_num at hn
  let a : ℝ × ℝ → ℝ := fun p =>
    (1 - Real.smoothTransition p.1) * r p.2 + Real.smoothTransition p.1
  have ha : ContDiff ℝ ∞ a :=
    ((contDiff_const.sub (Real.smoothTransition.contDiff.comp contDiff_fst)).mul
      (hr.comp contDiff_snd)).add (Real.smoothTransition.contDiff.comp contDiff_fst)
  have hapos (z s : ℝ) : 0 < a (z, s) := by
    dsimp only [a]
    by_cases hS : Real.smoothTransition z = 1
    · rw [hS]
      norm_num
    · have hSlt : Real.smoothTransition z < 1 :=
        lt_of_le_of_ne (Real.smoothTransition.le_one z) hS
      exact add_pos_of_pos_of_nonneg
        (mul_pos (sub_pos.mpr hSlt) (hrpos s)) (Real.smoothTransition.nonneg z)
  let H : ℝ × ℝ → E := fun p => a p • P p.2
  have hH : ContDiff ℝ ∞ H := ha.smul (hP.comp contDiff_snd)
  have hHper (z : ℝ) : Periodic (fun s => H (z, s)) T := by
    intro s
    have hpp : sphereCircleParameter e (B (s + T)) = sphereCircleParameter e (B s) := hphase s
    change ((1 - Real.smoothTransition z) * r (s + T) + Real.smoothTransition z) •
      (sphereCircleParameter e (B (s + T)) : E) = _
    rw [hrper s, hpp]
  have hnorm (z s : ℝ) : (unitRadialProjection q0 (H (z, s)) : E) = P s := by
    change (unitRadialProjection q0 (a (z, s) • (sphereCircleParameter e (B s) : E)) : E) = _
    rw [unitRadialProjection_pos_smul q0 (hapos z s), unitRadialProjection_apply_coe]
  have hHne (z s : ℝ) : H (z, s) ≠ 0 :=
    smul_ne_zero (hapos z s).ne' (ne_zero_of_mem_unit_sphere (sphereCircleParameter e (B s)))
  have hHi (z : ℝ) : InjOn (fun s => H (z, s)) (Ico 0 T) := by
    intro s hs t ht heq
    apply hPinj hs ht
    apply Subtype.ext
    have hh := congrArg (fun x : E => (unitRadialProjection q0 x : E)) heq
    simpa only [hnorm] using hh
  have hHd (z s : ℝ) : deriv (fun t => H (z, t)) s ≠ 0 := by
    intro hz
    have hHs : DifferentiableAt ℝ (fun t => H (z, t)) s :=
      ((hH.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) s)
    have hN : DifferentiableAt ℝ (fun x : E => (unitRadialProjection q0 x : E)) (H (z, s)) :=
      (contDiffAt_unitRadialProjection_coe (m := ∞) q0 (hHne z s)).differentiableAt (by simp)
    have hh := hN.hasFDerivAt.comp_hasDerivAt s hHs.hasDerivAt
    have hfun : (fun x : E => (unitRadialProjection q0 x : E)) ∘ (fun t => H (z, t)) = P :=
      funext (hnorm z)
    rw [hfun, hz, map_zero] at hh
    exact hPne s hh.deriv
  let c : ℝ → sphere (0 : E) 1 → E :=
    fun z => periodicCircleCurve T e (fun s => H (z, s))
  have hc : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × sphere (0 : E) 1 => c p.1 p.2) :=
    contMDiff_periodicCircleCurve_family hT e (fun z s => H (z, s)) hH hHper
  obtain ⟨F, _, _, _, _, _, hFrange⟩ := exists_supported_curve_family_transport e o q0 c hc
    (show (0 : ℝ) < 1 by norm_num)
    (fun z _ => injective_periodicCircleCurve hT e (hHper z) (hHi z))
    (fun z _ => mfderiv_periodicCircleCurve_injective hT e (hHper z)
      (hH.comp (contDiff_const.prodMk contDiff_id)) (hHd z))
  have hsurj : Surjective B := by
    have hτ : 0 < 2 * Real.pi := by positivity
    have hf : Continuous (fun s => (T / (2 * Real.pi)) * B s) :=
      continuous_const.mul hB.continuous
    have hp (s : ℝ) : (T / (2 * Real.pi)) * B (s + T) =
        (T / (2 * Real.pi)) * B s + T := by
      rw [htrans, mul_add, div_mul_cancel₀ _ hτ.ne']
    intro y
    obtain ⟨x, hx⟩ := surjective_of_add_period hT hf hp ((T / (2 * Real.pi)) * y)
    exact ⟨x, mul_left_cancel₀ (div_pos hT hτ).ne' hx⟩
  have hPrange : range P = sphere (0 : E) 1 := by
    apply subset_antisymm
    · rintro x ⟨s, rfl⟩
      exact (sphereCircleParameter e (B s)).2
    · intro x hx
      obtain ⟨s, hs⟩ := surjective_sphereCircleParameter e ⟨x, hx⟩
      obtain ⟨t, ht⟩ := hsurj s
      exact ⟨t, by change (sphereCircleParameter e (B t) : E) = x; rw [ht, hs]⟩
  have hzero : (fun s => H (0, s)) =
      (fun s => r s • (sphereCircleParameter e (B s) : E)) := by
    funext s
    simp only [H, a, Real.smoothTransition.zero, sub_zero, one_mul, add_zero, P]
  have hone : (fun s => H (1, s)) = P := by
    funext s
    simp only [H, a, Real.smoothTransition.one, sub_self, zero_mul, zero_add, one_smul]
  have hh := hFrange 1 (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)
  rw [range_comp'] at hh
  change F 1 '' range (periodicCircleCurve T e (fun s => H (0, s))) =
    range (periodicCircleCurve T e (fun s => H (1, s))) at hh
  rw [range_periodicCircleCurve hT e (hHper 0), range_periodicCircleCurve hT e (hHper 1),
    hzero, hone, hPrange] at hh
  exact ⟨F 1, hh⟩

end PoincareConjecture.M25.Topology3D
