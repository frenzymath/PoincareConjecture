import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.SphereCircle.ParallelDisks
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.SphereCircle.Tube.Reparametrization

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

theorem exists_parallel_cutting_charts
    {ε a : Real} (ha : 0 < a) (haε : a < ε / 4) (ha1 : a < 1 / 4)
    (T : OpenPartialHomeomorph (S1 × Real) S2)
    (hT : ContMDiffOn Iprod (𝓡 2) ∞ T T.source)
    (hTi : ContMDiffOn (𝓡 2) Iprod ∞ T.symm T.target)
    (hsource : T.source = univ ×ˢ Ioo (-ε) ε)
    (d : OpenPartialHomeomorph E2 S2)
    (hd : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source)
    (hdi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target)
    (hwide : closedBall 0 (1 + 2 * a) ⊆ d.source)
    (q : Diffeomorph (𝓡 1) (𝓡 1) S1 S1 ∞)
    (hmatch : ∀ p : S1, ∀ t : Real, |t| ≤ 2 * a ->
      d ((1 + t) • (p : E2)) = T (q p, t)) :
    ∃ eInner eOuter : OpenPartialHomeomorph E2 S2,
      closedBall 0 1 ⊆ eInner.source ∧ closedBall 0 1 ⊆ eOuter.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ eInner eInner.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ eInner.symm eInner.target ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ eOuter eOuter.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ eOuter.symm eOuter.target ∧
      eInner '' closedBall 0 1 = d '' closedBall 0 (1 + a) ∧
      eInner '' ball 0 1 = d '' ball 0 (1 + a) ∧
      eOuter '' closedBall 0 1 = (d '' ball 0 (1 - a))ᶜ ∧
      eOuter '' ball 0 1 = (d '' closedBall 0 (1 - a))ᶜ ∧
      ∃ TPlus TMinus : OpenPartialHomeomorph (S1 × Real) S2,
        TPlus.source = univ ×ˢ Ioo (-(a / 2)) (a / 2) ∧
        TMinus.source = univ ×ˢ Ioo (-(a / 2)) (a / 2) ∧
        ContMDiffOn Iprod (𝓡 2) ∞ TPlus TPlus.source ∧
        ContMDiffOn (𝓡 2) Iprod ∞ TPlus.symm TPlus.target ∧
        ContMDiffOn Iprod (𝓡 2) ∞ TMinus TMinus.source ∧
        ContMDiffOn (𝓡 2) Iprod ∞ TMinus.symm TMinus.target ∧
        (∀ p t, TPlus (p, t) = T (p, a + t)) ∧
        (∀ p t, TMinus (p, t) = T (p, -a - t)) ∧
        range (fun p : S1 => TPlus (p, 0)) = eInner '' sphere (0 : E2) 1 ∧
        range (fun p : S1 => TMinus (p, 0)) = eOuter '' sphere (0 : E2) 1 ∧
        (∀ p : S1, ∀ t ∈ Ioo (-(a / 2)) 0, TPlus (p, t) ∈ eInner '' ball 0 1) ∧
        (∀ p : S1, ∀ t ∈ Ioo (-(a / 2)) 0, TMinus (p, t) ∈ eOuter '' ball 0 1) := by
  have hminus : 0 < 1 - a := by linarith
  have hplus : 0 < 1 + a := by linarith
  have hsmallsource : closedBall (0 : E2) (1 - a) ⊆ d.source :=
    (closedBall_subset_closedBall (by linarith)).trans hwide
  have hbigsource : closedBall (0 : E2) (1 + a) ⊆ d.source :=
    (closedBall_subset_closedBall (by linarith)).trans hwide
  have htimepos {t : Real} (ht : |t| ≤ 2 * a) : 0 < 1 + t := by
    have hh := (abs_le.mp ht).1
    linarith
  have hradial {x : E2} (hx : 0 < ‖x‖) :
      ‖x‖ • (CircleCollar.direction x : E2) = x := by
    rw [CircleCollar.direction_coe (norm_pos_iff.mp hx), smul_smul,
      mul_inv_cancel₀ hx.ne', one_smul]
  have hsphere (t : Real) (ht : |t| ≤ 2 * a) :
      d '' sphere (0 : E2) (1 + t) = range (fun p : S1 => T (p, t)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hnorm := mem_sphere_zero_iff_norm.mp hx
      refine ⟨q (CircleCollar.direction x), ?_⟩
      have hh := hmatch (CircleCollar.direction x) t ht
      rw [← hnorm, hradial (hnorm.symm ▸ htimepos ht)] at hh
      exact hh.symm
    · rintro ⟨p, rfl⟩
      refine ⟨(1 + t) • ((q.symm p : S1) : E2), ?_, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
          abs_of_pos (htimepos ht), norm_eq_of_mem_sphere, mul_one]
      · rw [hmatch _ t ht, q.apply_symm_apply]
  obtain ⟨eInner, hIs, hI, hIi, hIc, hIb, hIsphere⟩ :=
    ParallelDisks.exists_rescaled_disk_chart hplus d hbigsource hd hdi
  let D : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 S2 ∞ :=
    { d with contMDiffOn_toFun := hd, contMDiffOn_invFun := hdi }
  obtain ⟨R, E, hR, hEs, hE, hEi, hEc⟩ := exists_complementary_disk_neighborhood
    hminus d (d.injOn.mono hsmallsource)
      (fun x hx => D.isLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ (hsmallsource hx))
  obtain ⟨eOuter, hOs, hO, hOi, hOc, _, _⟩ :=
    ParallelDisks.exists_rescaled_disk_chart hR E hEs hE hEi
  have hOuterClosed : eOuter '' closedBall 0 1 = (d '' ball 0 (1 - a))ᶜ := hOc.trans hEc
  have hOuterOpen : eOuter '' ball 0 1 = (d '' closedBall 0 (1 - a))ᶜ := by
    rw [eOuter.image_ball_eq_interior hOs hOuterClosed, interior_compl,
      ParallelDisks.closure_image_ball hminus d hsmallsource]
  have hOuterSphere : eOuter '' sphere (0 : E2) 1 = range (fun p : S1 => T (p, -a)) := by
    rw [eOuter.image_sphere_eq_frontier hOs hOuterClosed, frontier_compl,
      ParallelDisks.frontier_image_ball hminus d hsmallsource hd hdi]
    convert! hsphere (-a) (by rw [abs_neg, abs_of_pos ha]; linarith) using 1
  obtain ⟨TPlus, hPs, hP, hPi, hPformula⟩ := exists_reparametrized_sphere_tube
    T hT hTi hsource a 1 one_ne_zero (r := a / 2) (by positivity)
      (by rw [abs_of_pos ha, abs_one, one_mul]; linarith)
  obtain ⟨TMinus, hMs, hM, hMi, hMformula⟩ := exists_reparametrized_sphere_tube
    T hT hTi hsource (-a) (-1) (by norm_num) (r := a / 2) (by positivity)
      (by rw [abs_neg, abs_of_pos ha, abs_neg, abs_one, one_mul]; linarith)
  have hPlus (p : S1) (t : Real) : TPlus (p, t) = T (p, a + t) := by
    simpa only [one_mul] using hPformula p t
  have hMinus (p : S1) (t : Real) : TMinus (p, t) = T (p, -a - t) := by
    simpa only [neg_one_mul, sub_eq_add_neg] using hMformula p t
  refine ⟨eInner, eOuter, hIs, hOs, hI, hIi, hO, hOi, hIc, hIb,
    hOuterClosed, hOuterOpen, TPlus, TMinus, hPs, hMs, hP, hPi, hM, hMi,
    hPlus, hMinus, ?_, ?_, ?_, ?_⟩
  · rw [hIsphere, hsphere a (by rw [abs_of_pos ha]; linarith)]
    apply congrArg range
    funext p
    simpa only [add_zero] using hPlus p 0
  · rw [hOuterSphere]
    apply congrArg range
    funext p
    simpa only [sub_zero] using hMinus p 0
  · intro p t ht
    have htime : |a + t| ≤ 2 * a := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have heq := hmatch (q.symm p) (a + t) htime
    rw [q.apply_symm_apply] at heq
    rw [hIb, hPlus, ← heq]
    refine mem_image_of_mem d ?_
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (htimepos htime), norm_eq_of_mem_sphere, mul_one]
    linarith [ht.2]
  · intro p t ht
    have htime : |-a - t| ≤ 2 * a := abs_le.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have heq := hmatch (q.symm p) (-a - t) htime
    rw [q.apply_symm_apply] at heq
    rw [hOuterOpen, hMinus, ← heq]
    have hxs : (1 + (-a - t)) • ((q.symm p : S1) : E2) ∈ d.source := by
      apply hwide
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
        abs_of_pos (htimepos htime), norm_eq_of_mem_sphere, mul_one]
      linarith [ht.1]
    rintro ⟨z, hz, hzd⟩
    have hzval := d.injOn (hsmallsource hz) hxs hzd
    have hznorm := mem_closedBall_zero_iff.mp hz
    rw [hzval, norm_smul, Real.norm_eq_abs, abs_of_pos (htimepos htime),
      norm_eq_of_mem_sphere, mul_one] at hznorm
    linarith [ht.2]

end Poincare.Manifold.Schoenflies
