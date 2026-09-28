import PoincareConjecture.Proofs.M25.AppA_1_Necks.TransitionHeight
import PoincareConjecture.Proofs.M25.Mathlib.ClosedPrefixTrap
import Mathlib.Analysis.Calculus.MeanValue










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck




theorem exists_signed_axial_line_control :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (A D : EpsilonNeck g),
      A.epsilon ≤ epsilon0 → D.epsilon = A.epsilon →
      ∀ (q : UnitTwoSphere) (s0 s1 sigma c d : ℝ),
        s0 ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹ →
        s1 ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹ →
        (sigma = 1 ∨ sigma = -1) →
        A.coordinate_map (q, s0) ∈ D.carrier →
        0 < sigma * (D.scale * mvfderiv (𝓡 3)
          (fun x => (D.coordinate_inverse x).2) (A.coordinate_map (q, s0))
          (A.normalizedAxialVector (A.coordinate_map (q, s0)))) →
        -D.epsilon⁻¹ < c → d < D.epsilon⁻¹ →
        (∀ t ∈ uIcc s0 s1,
          c ≤ (D.coordinate_inverse (A.coordinate_map (q, s0))).2 +
              sigma * (t - s0) - (1 / 100 : ℝ) * |t - s0| ∧
            (D.coordinate_inverse (A.coordinate_map (q, s0))).2 +
                sigma * (t - s0) + (1 / 100 : ℝ) * |t - s0| ≤ d) →
        ∀ t ∈ uIcc s0 s1,
          A.coordinate_map (q, t) ∈ D.carrier ∧
          (D.coordinate_inverse (A.coordinate_map (q, t))).2 ∈ Icc c d ∧
          |(D.coordinate_inverse (A.coordinate_map (q, t))).2 -
              (D.coordinate_inverse (A.coordinate_map (q, s0))).2 -
                sigma * (t - s0)| ≤ (1 / 100 : ℝ) * |t - s0| ∧
          0 < sigma * (D.scale * mvfderiv (𝓡 3)
            (fun x => (D.coordinate_inverse x).2) (A.coordinate_map (q, t))
            (A.normalizedAxialVector (A.coordinate_map (q, t)))) := by
  obtain ⟨es, hspos, hscap, hscale⟩ :=
    exists_intersecting_scale_control.{u} (α := (1 / 1000 : ℝ)) (by norm_num)
  obtain ⟨eo, hopos, _, horient⟩ :=
    exists_intersecting_coherent_orientation.{u} (η := (1 / 1000 : ℝ))
      (by constructor <;> norm_num)
  refine ⟨min es eo, lt_min hspos hopos, (min_le_left _ _).trans hscap, ?_⟩
  intro M _ _ _ _ _ _ g A D hA he q s0 s1 sigma c d
    hs0 hs1 hsigma hstart hsign hc hd henvelope
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  have hAs : A.epsilon ≤ es := hA.trans (min_le_left _ _)
  have hDs : D.epsilon ≤ es := by rw [he]; exact hAs
  have hAo : A.epsilon ≤ eo := hA.trans (min_le_right _ _)
  have hDo : D.epsilon ≤ eo := by rw [he]; exact hAo
  let I : Set ℝ := uIcc s0 s1
  let gamma : ℝ → M := fun t => A.coordinate_map (q, t)
  let h : ℝ → ℝ := fun t => (D.coordinate_inverse (gamma t)).2
  let b : ℝ → ℝ := fun t => D.scale * mvfderiv (𝓡 3)
    (fun x => (D.coordinate_inverse x).2) (gamma t) (A.normalizedAxialVector (gamma t))
  change 0 < sigma * b s0 at hsign
  change ∀ t ∈ I, gamma t ∈ D.carrier ∧ h t ∈ Icc c d ∧
    |h t - h s0 - sigma * (t - s0)| ≤ (1 / 100 : ℝ) * |t - s0| ∧
    0 < sigma * b t
  have hstrip (t : ℝ) (ht : t ∈ I) : t ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹ := by
    change t ∈ uIcc s0 s1 at ht
    rcases le_total s0 s1 with hs | hs
    · rw [uIcc_of_le hs] at ht
      exact ⟨hs0.1.trans_le ht.1, ht.2.trans_lt hs1.2⟩
    · rw [uIcc_of_ge hs] at ht
      exact ⟨hs1.1.trans_le ht.1, ht.2.trans_lt hs0.2⟩
  have hgamma : ContinuousOn gamma I := by
    apply A.coordinate_map_smooth.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
    intro t ht
    exact ⟨mem_univ _, hstrip t ht⟩
  have hratio : |A.scale / D.scale - 1| < (1 / 1000 : ℝ) :=
    (hscale D A hDs hAs
      ⟨gamma s0, hstart, A.coordinate_map_mem ⟨mem_univ _, hs0⟩⟩).2
  have hr : A.scale / D.scale ≤ 2 := by linarith [(abs_lt.mp hratio).2]
  let K : Set M := D.coordinate_map '' (univ ×ˢ Icc c d)
  have hKclosed : IsClosed K := (D.isCompact_coordinate_slab hc hd).isClosed
  have hKsub : K ⊆ D.carrier := by
    rintro x ⟨z, hz, rfl⟩
    exact D.coordinate_map_mem
      ⟨mem_univ _, hc.trans_le hz.2.1, hz.2.2.trans_lt hd⟩

  have hprefix (t : ℝ) (ht : t ∈ I)
      (hpref : MapsTo gamma (uIcc s0 t) D.carrier) :
      h t ∈ Icc c d ∧
        |h t - h s0 - sigma * (t - s0)| ≤ (1 / 100 : ℝ) * |t - s0| ∧
        0 < sigma * b t := by
    have hsub : uIcc s0 t ⊆ I := uIcc_subset_uIcc_left ht
    let S : Set RoundCylinderSpace := {q} ×ˢ uIcc s0 t
    have hpre : IsPreconnected S := isPreconnected_singleton.prod isPreconnected_uIcc
    have hret : S ⊆ A.cylinderDomain ∩ A.coordinate_map ⁻¹' D.carrier := by
      rintro ⟨p, r⟩ ⟨hp, hrmem⟩
      have hpq : p = q := mem_singleton_iff.mp hp
      subst p
      exact ⟨⟨mem_univ _, hstrip r (hsub hrmem)⟩, hpref hrmem⟩
    obtain ⟨rho, hrho, hcross0⟩ := horient A D hAo hDo S hpre hret
    have hcross (r : ℝ) (hrmem : r ∈ uIcc s0 t) :
        |1 - rho * b r| < (1 / 1000 : ℝ) := by
      simpa only [b, gamma, mul_assoc] using
        hcross0 (q, r) ⟨mem_singleton _, hrmem⟩
    have heq : rho = sigma := by
      have h0 := hcross s0 left_mem_uIcc
      rcases hrho with rfl | rfl <;> rcases hsigma with rfl | rfl
      · rfl
      · exfalso
        norm_num at h0 hsign
        linarith [(abs_lt.mp h0).2]
      · exfalso
        norm_num at h0 hsign
        linarith [(abs_lt.mp h0).2]
      · rfl
    rw [heq] at hcross
    have hdiff (r : ℝ) (hrmem : r ∈ uIcc s0 t) : DifferentiableAt ℝ h r := by
      have hz : (q, r) ∈ A.cylinderDomain := ⟨mem_univ _, hstrip r (hsub hrmem)⟩
      have hm := A.coordinate_map_smooth.contMDiffAt (A.cylinderDomain_open.mem_nhds hz)
      have hi := D.coordinate_inverse_smooth.contMDiffAt
        (D.carrier_open.mem_nhds (hpref hrmem))
      have hp : ContMDiffAt 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
          (fun r : ℝ => (q, r)) r := contMDiffAt_const.prodMk contMDiffAt_id
      exact mdifferentiableAt_iff_differentiableAt.mp
        ((contMDiffAt_snd.comp r (hi.comp r (hm.comp r hp))).mdifferentiableAt (by simp))
    have hderiv (r : ℝ) (hrmem : r ∈ uIcc s0 t) :
        |deriv h r - sigma| ≤ 3 * (1 / 1000 : ℝ) := by
      exact A.transition_height_axial_error D
        ⟨mem_univ _, hstrip r (hsub hrmem)⟩ (hpref hrmem)
        hsigma (by norm_num) hratio.le hr (hcross r hrmem).le
    let G : ℝ → ℝ := fun r => h r - sigma * (r - s0)
    have hGdiff (r : ℝ) (hrmem : r ∈ uIcc s0 t) : DifferentiableAt ℝ G r :=
      (hdiff r hrmem).sub ((differentiableAt_id.sub_const s0).const_mul sigma)
    have hGderiv (r : ℝ) (hrmem : r ∈ uIcc s0 t) :
        deriv G r = deriv h r - sigma := by
      have hfun : (h - fun y => sigma * (id y - s0)) = G := rfl
      simpa only [hfun, mul_one] using
        ((hdiff r hrmem).hasDerivAt.sub
          (((hasDerivAt_id r).sub_const s0).const_mul sigma)).deriv
    have hGbound (r : ℝ) (hrmem : r ∈ uIcc s0 t) :
        ‖deriv G r‖ ≤ 3 * (1 / 1000 : ℝ) := by
      rw [hGderiv r hrmem, Real.norm_eq_abs]
      exact hderiv r hrmem
    have herror : |h t - h s0 - sigma * (t - s0)| ≤
        (1 / 100 : ℝ) * |t - s0| := by
      have hm := Convex.norm_image_sub_le_of_norm_deriv_le hGdiff hGbound
        (convex_uIcc s0 t) left_mem_uIcc right_mem_uIcc
      have hG0 : G s0 = h s0 := by simp only [G, sub_self, mul_zero, sub_zero]
      have hform : G t - h s0 = h t - h s0 - sigma * (t - s0) := by
        dsimp only [G]
        ring
      rw [hG0, hform, Real.norm_eq_abs, Real.norm_eq_abs] at hm
      exact hm.trans (mul_le_mul_of_nonneg_right (by norm_num) (abs_nonneg _))
    have hbounds := henvelope t ht
    change c ≤ h s0 + sigma * (t - s0) - (1 / 100 : ℝ) * |t - s0| ∧
      h s0 + sigma * (t - s0) + (1 / 100 : ℝ) * |t - s0| ≤ d at hbounds
    have hheight : h t ∈ Icc c d := by
      have he := abs_le.mp herror
      constructor <;> linarith [hbounds.1, hbounds.2, he.1, he.2]
    refine ⟨hheight, herror, ?_⟩
    linarith [(abs_lt.mp (hcross t right_mem_uIcc)).2]
  have hguard : K ∩ gamma '' I ⊆ D.carrier := fun _ hx => hKsub hx.1
  have htrap (t : ℝ) (ht : t ∈ I)
      (hpref : MapsTo gamma (uIcc s0 t) D.carrier) : gamma t ∈ K := by
    exact ⟨D.coordinate_inverse (gamma t),
      ⟨mem_univ _, (hprefix t ht hpref).1⟩,
      D.coordinate_map_inverse (hpref right_mem_uIcc)⟩
  have hpath : MapsTo gamma I D.carrier :=
    hgamma.mapsTo_uIcc_of_closed_prefix_trap D.carrier_open hKclosed hstart hguard htrap
  intro t ht
  exact ⟨hpath ht, hprefix t ht (fun _ hrmem => hpath (uIcc_subset_uIcc_left ht hrmem))⟩

end PoincareConjecture.EpsilonNeck
