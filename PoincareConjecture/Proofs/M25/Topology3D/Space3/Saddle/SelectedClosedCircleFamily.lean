import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedLevelGluing
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarHeight
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Analysis.SpecialFunctions.SmoothTransition











set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D


set_option linter.unusedVariables false in



theorem exists_saddle_selected_closed_circle_family
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (c rho delta : ℝ)
    (hrho : 0 < rho) (hdelta : 0 < delta)
    (hsmall : delta ≤ rho ^ 2 / 128)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (ks : OpenPartialHomeomorph E2 UnitTwoSphere)
    (kp : OpenPartialHomeomorph E2 E2)
    (hksSource : closedBall (0 : E2) 2 ⊆ ks.source)
    (hkpSource : closedBall (0 : E2) 2 ⊆ kp.source)
    (hks : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ ks ks.source)
    (hksInv : ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ ks.symm ks.target)
    (hkp : ContDiffOn ℝ ∞ kp kp.source)
    (hkpInv : ContDiffOn ℝ ∞ kp.symm kp.target)
    (n : ℕ) (q : Fin n → UnitCircle → UnitTwoSphere)
    (hq : ∀ i : Fin n,
      ContMDiff (𝓡 1) (𝓡 2) ∞ (q i) ∧ Function.Injective (q i) ∧
      ∀ p : UnitCircle, Function.Injective (mfderiv (𝓡 1) (𝓡 2) (q i) p))
    (hqd : ∀ i j : Fin n, i ≠ j → Disjoint (range (q i)) (range (q j)))
    (Phi : ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞)
    (hPhi : ContDiff ℝ ∞ (fun p : ℝ × E3 => Phi p.1 p.2))
    (hPhiZero : ∀ y : E3, Phi 0 y = y)
    (F : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (hF : ContDiff ℝ ∞ (fun p : ℝ × E2 => F p.1 p.2))
    (hFNorm : ∀ t x, ‖F t x‖ = ‖x‖)
    (hFZero : ∀ t x, t ≤ 0 → F t x = x)
    (hFOne : ∀ t x, 1 ≤ t → F t x = F 1 x) :
    let j : UnitTwoSphere → E3 := fun p => psi (p, 0)
    let L := heightPlaneCoordinates u
    let pi := horizontalBandProjection u
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let S := range j
    let sigma : ℝ → ℝ := Real.smoothTransition
    let K := kp '' closedBall (0 : E2) 1
    let V := kp '' ball (0 : E2) 1
    let Cs := ks '' closedBall (0 : E2) 1
    let Vs := ks '' ball (0 : E2) 1
    let Elevel : ℝ → Set E3 := fun z => (S ∩ {y | H y = c + z}) \ (j '' Vs)
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let X : ℝ → ℝ → Fin 4 → E2 := fun a r i => J2.symm
      (sx i * Real.sqrt ((r ^ 2 + a) / 2),
        sy i * Real.sqrt ((r ^ 2 - a) / 2))
    ∀ (hCoordinates : ∀ x ∈ closedBall (0 : E2) 2,
        pi (j (ks x)) = kp x ∧
        H (j (ks x)) = c + rho ^ 2 * ((J2 x).1 ^ 2 - (J2 x).2 ^ 2))
      (hNoSheets : ∀ z : ℝ, |z| ≤ 2 * delta → ∀ p : UnitTwoSphere,
        H (j p) = c + z →
        (pi (j p) ∈ V ↔ p ∈ Vs) ∧ (pi (j p) ∈ K ↔ p ∈ Cs))
      (hLevel : ⋃ i : Fin n, range (q i) = {p : UnitTwoSphere | H (j p) = c - delta})
      (hExterior : ∀ tau ∈ Icc (0 : ℝ) delta,
        Phi tau '' Elevel (-delta) = Elevel (-delta + tau))
      (hNative : ∀ tau ∈ Icc (0 : ℝ) delta, ∀ i : Fin 4,
        ∀ a ∈ Ioo (-(1 / 8) : ℝ) (1 / 8),
          Phi tau (j (ks (X (-delta / rho ^ 2) (1 + a) i))) =
            j (ks (X ((-delta + tau) / rho ^ 2) (1 + a) i)))
      (hAngular : ∀ t : ℝ, ∀ i : Fin 4,
        ∀ a ∈ Ioo (-(1 / 8) : ℝ) (1 / 8),
          F t (X (-delta / rho ^ 2) (1 + a) i) =
            X ((-delta + sigma t * delta) / rho ^ 2) (1 + a) i),
      ∃ C : ℝ → Fin n → UnitCircle → E2,
        (∀ i : Fin n,
          ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
            (fun p : ℝ × UnitCircle => C p.1 i p.2)) ∧
        (∀ t i, IsPlanarEmbedding (C t i)) ∧
        (∀ t i k, i ≠ k → Disjoint (range (C t i)) (range (C t k))) ∧
        (∀ t i theta, t ≤ 0 → C t i theta = pi (j (q i theta))) ∧
        (∀ t i theta, 1 ≤ t → C t i theta = C 1 i theta) ∧
        (∀ t i theta, q i theta ∈ Cs →
          C t i theta = kp (F t (ks.symm (q i theta)))) ∧
        (∀ t i theta, q i theta ∉ Vs →
          C t i theta = pi (Phi (sigma t * delta) (j (q i theta)))) ∧
        (∀ t, (⋃ i : Fin n, range (C t i)) \ V =
          {x : E2 | L.symm (x, c - delta + sigma t * delta) ∈ S} \ V) ∧
        (∀ t, (⋃ i : Fin n, range (C t i)) ∩ K =
          kp '' ((F t) '' {x : E2 | ‖x‖ ≤ 1 ∧
            rho ^ 2 * ((J2 x).1 ^ 2 - (J2 x).2 ^ 2) = -delta})) ∧
        (∀ i : Fin n, Disjoint (range (q i)) Cs →
          (∀ t theta, C t i theta =
            pi (Phi (sigma t * delta) (j (q i theta)))) ∧
          ∀ t, Disjoint (range (C t i)) K) := by
  classical
  let j : UnitTwoSphere → E3 := fun p => psi (p, 0)
  let L := heightPlaneCoordinates u
  let pi := horizontalBandProjection u
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  let S := range j
  let sigma : ℝ → ℝ := Real.smoothTransition
  let K := kp '' closedBall (0 : E2) 1
  let V := kp '' ball (0 : E2) 1
  let Cs := ks '' closedBall (0 : E2) 1
  let Vs := ks '' ball (0 : E2) 1
  let Elevel : ℝ → Set E3 := fun z => (S ∩ {y | H y = c + z}) \ (j '' Vs)
  dsimp only
  intro hCoordinates hNoSheets hLevel hExterior hNative hAngular
  change ∀ x ∈ closedBall (0 : E2) 2,
    pi (j (ks x)) = kp x ∧
      H (j (ks x)) = c + rho ^ 2 * ((J2 x).1 ^ 2 - (J2 x).2 ^ 2) at hCoordinates
  change (⋃ i : Fin n, range (q i)) = {p : UnitTwoSphere | H (j p) = c - delta} at hLevel
  change ∀ tau ∈ Icc (0 : ℝ) delta,
    Phi tau '' Elevel (-delta) = Elevel (-delta + tau) at hExterior
  let N : Set UnitTwoSphere := {p | H (j p) = c - delta}
  let A : ℝ → UnitTwoSphere → E2 := fun t p =>
    if p ∈ Vs then kp (F t (ks.symm p)) else pi (Phi (sigma t * delta) (j p))
  obtain ⟨hAi, hAm, hOverlap, hAe, hAk⟩ :=
    saddle_selected_level_gluing psi hpsi u c rho delta hrho hdelta hsmall J2 hJ2
      ks kp hksSource hkpSource Phi F hFNorm
      hCoordinates hNoSheets hExterior hNative hAngular
  change ∀ t : ℝ, InjOn (A t) N at hAi
  change ∀ t : ℝ, ∀ p ∈ N,
    (A t p ∈ V ↔ p ∈ Vs) ∧ (A t p ∈ K ↔ p ∈ Cs) ∧
    (p ∈ Cs → A t p = kp (F t (ks.symm p))) ∧
    (p ∉ Vs → A t p = pi (Phi (sigma t * delta) (j p))) at hAm
  change ∀ t : ℝ, (A t '' N) \ V =
    {x : E2 | L.symm (x, c - delta + sigma t * delta) ∈ S} \ V at hAe
  change ∀ t : ℝ, (A t '' N) ∩ K =
    kp '' ((F t) '' {x : E2 | ‖x‖ ≤ 1 ∧
      rho ^ 2 * ((J2 x).1 ^ 2 - (J2 x).2 ^ 2) = -delta}) at hAk
  let C : ℝ → Fin n → UnitCircle → E2 := fun t i theta => A t (q i theta)
  let B : ℝ → Fin n → UnitCircle → E2 := fun t i theta =>
    kp (F t (ks.symm (q i theta)))
  let Y : ℝ → Fin n → UnitCircle → E3 := fun t i theta =>
    Phi (sigma t * delta) (j (q i theta))
  have hqN (i : Fin n) (theta : UnitCircle) : q i theta ∈ N := by
    change q i theta ∈ {p | H (j p) = c - delta}
    rw [← hLevel]
    exact mem_iUnion.mpr ⟨i, ⟨theta, rfl⟩⟩
  have hs2 {x : E2} (hx : ‖x‖ ≤ 2) : x ∈ ks.source :=
    hksSource (by simpa only [mem_closedBall, dist_zero_right] using hx)
  have hp2 {x : E2} (hx : ‖x‖ ≤ 2) : x ∈ kp.source :=
    hkpSource (by simpa only [mem_closedBall, dist_zero_right] using hx)
  have hsc {p : UnitTwoSphere} (hp : p ∈ Cs) :
      p ∈ ks.target ∧ ‖ks.symm p‖ ≤ 1 := by
    obtain ⟨x, hx, rfl⟩ := hp
    have hxn : ‖x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hx
    have hxs := hs2 (by linarith)
    exact ⟨ks.map_source hxs, by simpa only [ks.left_inv hxs] using hxn⟩
  have hVsCs : Vs ⊆ Cs := image_mono ball_subset_closedBall
  have hCsClosed : IsClosed Cs :=
    ((isCompact_closedBall (0 : E2) 1).image_of_continuousOn
      (ks.continuousOn.mono (fun x hx => hs2 (by
        have hn : ‖x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hx
        linarith)))).isClosed
  let U : Set UnitTwoSphere := ks '' ball (0 : E2) (9 / 8)
  have hU : IsOpen U := ks.isOpen_image_of_subset_source isOpen_ball (by
    intro x hx
    have hn : ‖x‖ < 9 / 8 := by simpa only [mem_ball, dist_zero_right] using hx
    exact hs2 (by linarith))
  have hCsU : Cs ⊆ U := image_mono (by
    intro x hx
    have hn : ‖x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hx
    simpa only [mem_ball, dist_zero_right] using (show ‖x‖ < (9 / 8 : ℝ) by linarith))
  have hu {p : UnitTwoSphere} (hp : p ∈ U) :
      p ∈ ks.target ∧ ‖ks.symm p‖ < 9 / 8 := by
    obtain ⟨x, hx, rfl⟩ := hp
    have hn : ‖x‖ < 9 / 8 := by simpa only [mem_ball, dist_zero_right] using hx
    have hxs := hs2 (by linarith)
    exact ⟨ks.map_source hxs, by simpa only [ks.left_inv hxs] using hn⟩
  have hInner (t : ℝ) (p : UnitTwoSphere) (hpN : p ∈ N) (hpU : p ∈ U) :
      A t p = kp (F t (ks.symm p)) := by
    by_cases hpV : p ∈ Vs
    · simp only [A, if_pos hpV]
    · have ht := hu hpU
      have hn : 1 ≤ ‖ks.symm p‖ := by
        by_contra hh
        apply hpV
        exact ⟨ks.symm p,
          by simpa only [mem_ball, dist_zero_right] using lt_of_not_ge hh,
          ks.right_inv ht.1⟩
      exact ((hAm t p hpN).2.2.2 hpV).trans
        (hOverlap t p hpN ht.1 (by linarith) ht.2).symm
  have hj : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ j := collar_central_contMDiff psi hpsi
  have hji : Injective j := by
    intro p q hpq
    exact congrArg Prod.fst (hpsi.2.1 (x₁ := (p, 0)) (x₂ := (q, 0))
      ⟨mem_univ _, by norm_num⟩ ⟨mem_univ _, by norm_num⟩ hpq)
  have hksD : ks.MDifferentiable 𝓘(ℝ, E2) (𝓡 2) :=
    ⟨hks.mdifferentiableOn (by simp), hksInv.mdifferentiableOn (by simp)⟩
  have hkpD : kp.MDifferentiable 𝓘(ℝ, E2) 𝓘(ℝ, E2) :=
    ⟨hkp.contMDiffOn.mdifferentiableOn (by simp),
      hkpInv.contMDiffOn.mdifferentiableOn (by simp)⟩
  have htau : ContDiff ℝ ∞ (fun t : ℝ => sigma t * delta) :=
    Real.smoothTransition.contDiff.mul contDiff_const
  have hqs (i : Fin n) :
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) (𝓡 2) ∞
        (fun w : ℝ × UnitCircle => q i w.2) := (hq i).1.comp contMDiff_snd
  have hYsm (i : Fin n) :
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E3) ∞
        (fun w : ℝ × UnitCircle => Y w.1 i w.2) :=
    hPhi.contMDiff.comp
      ((htau.contMDiff.comp contMDiff_fst).prodMk_space (hj.comp (hqs i)))
  have hOsm (i : Fin n) :
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
        (fun w : ℝ × UnitCircle => pi (Y w.1 i w.2)) :=
    pi.contDiff.contMDiff.comp (hYsm i)
  have hBsm (i : Fin n) (w : ℝ × UnitCircle) (hw : q i w.2 ∈ U) :
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
        (fun v : ℝ × UnitCircle => B v.1 i v.2) w := by
    have hv := hu hw
    have hInv := (hksInv.contMDiffAt (ks.open_target.mem_nhds hv.1)).comp w
      (hqs i).contMDiffAt
    have hFlow := hF.contMDiff.contMDiffAt.comp w
      (contMDiff_fst.contMDiffAt.prodMk_space hInv)
    have hFt : F w.1 (ks.symm (q i w.2)) ∈ kp.source := hp2 (by
      rw [hFNorm]
      linarith [hv.2])
    exact (hkp.contMDiffOn.contMDiffAt (kp.open_source.mem_nhds hFt)).comp w hFlow
  have hCsm (i : Fin n) :
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
        (fun w : ℝ × UnitCircle => C w.1 i w.2) := by
    intro w
    by_cases hw : q i w.2 ∈ Cs
    · apply (hBsm i w (hCsU hw)).congr_of_eventuallyEq
      filter_upwards [(hU.preimage (hqs i).continuous).mem_nhds (hCsU hw)] with v hv
      exact hInner v.1 (q i v.2) (hqN i v.2) hv
    · apply (hOsm i).contMDiffAt.congr_of_eventuallyEq
      filter_upwards [(hCsClosed.isOpen_compl.preimage (hqs i).continuous).mem_nhds hw]
        with v hv
      exact (hAm v.1 (q i v.2) (hqN i v.2)).2.2.2 (fun h => hv (hVsCs h))
  have hCt (t : ℝ) (i : Fin n) : ContMDiff (𝓡 1) 𝓘(ℝ, E2) ∞ (C t i) :=
    (hCsm i).comp (contMDiff_const.prodMk contMDiff_id)
  have hYd (t : ℝ) (i : Fin n) (theta : UnitCircle) :
      Injective (mfderiv (𝓡 1) 𝓘(ℝ, E3) (Y t i) theta) := by
    have hd0 := (hj.mdifferentiable (by simp) (q i theta)).hasMFDerivAt.comp theta
      ((hq i).1.mdifferentiable (by simp) theta).hasMFDerivAt
    have hd1 := ((Phi (sigma t * delta)).mdifferentiable (by simp)
      (j (q i theta))).hasMFDerivAt.comp theta hd0
    have hi := ((Phi (sigma t * delta)).toOpenPartialHomeomorph_mdifferentiable
      (by simp)).mfderiv_injective (x := j (q i theta)) (mem_univ _)
    change Injective (mfderiv (𝓡 1) 𝓘(ℝ, E3)
      ((Phi (sigma t * delta) : E3 → E3) ∘ (j ∘ q i)) theta)
    rw [hd1.mfderiv]
    exact hi.comp ((collar_central_mfderiv_injective psi hpsi (q i theta)).comp
      ((hq i).2.2 theta))
  have hOutsideHeight (t : ℝ) (p : UnitTwoSphere) (hp : p ∈ N) (hv : p ∉ Vs) :
      H (Phi (sigma t * delta) (j p)) = c - delta + sigma t * delta := by
    have he : j p ∈ Elevel (-delta) := by
      refine ⟨⟨⟨p, rfl⟩, ?_⟩, ?_⟩
      · change H (j p) = c + -delta
        exact (show H (j p) = c - delta from hp).trans (by ring)
      · rintro ⟨p', hp', heq⟩
        exact hv ((hji heq) ▸ hp')
    have ht : sigma t * delta ∈ Icc (0 : ℝ) delta :=
      ⟨mul_nonneg (Real.smoothTransition.nonneg t) hdelta.le,
        (mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one t) hdelta.le).trans_eq
          (one_mul delta)⟩
    have he' := (hExterior (sigma t * delta) ht).subset ⟨j p, he, rfl⟩
    have hh : H (Phi (sigma t * delta) (j p)) = c + (-delta + sigma t * delta) := he'.1.2
    linarith
  have hCd (t : ℝ) (i : Fin n) (theta : UnitCircle) :
      Injective (mfderiv (𝓡 1) 𝓘(ℝ, E2) (C t i) theta) := by
    by_cases hp : q i theta ∈ Cs
    · have hv := hsc hp
      have hnear : C t i =ᶠ[𝓝 theta] B t i := by
        filter_upwards [(hU.preimage (hq i).1.continuous).mem_nhds (hCsU hp)] with eta heta
        exact hInner t (q i eta) (hqN i eta) heta
      have hd0 := (hksD.mdifferentiableAt_symm hv.1).hasMFDerivAt.comp theta
        ((hq i).1.mdifferentiable (by simp) theta).hasMFDerivAt
      have hd1 := ((F t).mdifferentiable (by simp) (ks.symm (q i theta))).hasMFDerivAt.comp
        theta hd0
      have hFt : F t (ks.symm (q i theta)) ∈ kp.source := hp2 (by
        rw [hFNorm]
        linarith [hv.2])
      have hd2 := (hkpD.mdifferentiableAt hFt).hasMFDerivAt.comp theta hd1
      have hiF := ((F t).toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv_injective
        (x := ks.symm (q i theta)) (mem_univ _)
      rw [hnear.mfderiv_eq]
      change Injective (mfderiv (𝓡 1) 𝓘(ℝ, E2)
        ((kp : E2 → E2) ∘ ((F t : E2 → E2) ∘ ((ks.symm : UnitTwoSphere → E2) ∘ q i))) theta)
      rw [hd2.mfderiv]
      exact (hkpD.mfderiv_injective hFt).comp
        (hiF.comp ((hksD.symm.mfderiv_injective hv.1).comp ((hq i).2.2 theta)))
    · let R : E2 → E3 := fun x => L.symm (x, c - delta + sigma t * delta)
      have hR : ContDiff ℝ ∞ R :=
        L.symm.contDiff.comp (contDiff_id.prodMk contDiff_const)
      have hrec : R ∘ C t i =ᶠ[𝓝 theta] Y t i := by
        filter_upwards [(hCsClosed.isOpen_compl.preimage (hq i).1.continuous).mem_nhds hp]
          with eta heta
        have hv : q i eta ∉ Vs := fun h => heta (hVsCs h)
        have hc := (hAm t (q i eta) (hqN i eta)).2.2.2 hv
        change L.symm (A t (q i eta), c - delta + sigma t * delta) = Y t i eta
        rw [hc]
        exact heightPlaneCoordinates_reconstruct u _ _ (hOutsideHeight t _ (hqN i eta) hv)
      have hd := (hR.contMDiff.mdifferentiable (by simp) (C t i theta)).hasMFDerivAt.comp
        theta ((hCt t i).mdifferentiable (by simp) theta).hasMFDerivAt
      have hchain := hd.mfderiv
      rw [hrec.mfderiv_eq] at hchain
      intro a b hab
      apply hYd t i theta
      rw [hchain]
      exact congrArg (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E3) R (C t i theta)) hab
  have hUnion (t : ℝ) : (⋃ i : Fin n, range (C t i)) = A t '' N := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, theta, htheta⟩ := mem_iUnion.mp hx
      exact ⟨q i theta, hqN i theta, htheta⟩
    · rintro ⟨p, hp, rfl⟩
      have hp' : p ∈ ⋃ i : Fin n, range (q i) := by
        rw [hLevel]
        exact hp
      obtain ⟨i, theta, htheta⟩ := mem_iUnion.mp hp'
      exact mem_iUnion.mpr ⟨i, ⟨theta, congrArg (A t) htheta⟩⟩
  refine ⟨C, hCsm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t i
    refine ⟨hCt t i, ?_, hCd t i⟩
    intro theta eta heq
    exact (hq i).2.1 (hAi t (hqN i theta) (hqN i eta) heq)
  · intro t i k hik
    apply disjoint_left.mpr
    intro x hx hk
    obtain ⟨theta, rfl⟩ := hx
    obtain ⟨eta, heq⟩ := hk
    have he := hAi t (hqN k eta) (hqN i theta) heq
    exact disjoint_left.mp (hqd i k hik) ⟨theta, rfl⟩ ⟨eta, he⟩
  · intro t i theta ht
    by_cases hp : q i theta ∈ Vs
    · have hv := hsc (hVsCs hp)
      have hh := (hCoordinates (ks.symm (q i theta)) (by
        simpa only [mem_closedBall, dist_zero_right] using
          (show ‖ks.symm (q i theta)‖ ≤ 2 by linarith [hv.2]))).1
      rw [ks.right_inv hv.1] at hh
      change A t (q i theta) = pi (j (q i theta))
      simp only [A, if_pos hp, hFZero t _ ht]
      exact hh.symm
    · change A t (q i theta) = pi (j (q i theta))
      rw [(hAm t (q i theta) (hqN i theta)).2.2.2 hp]
      simp only [sigma, Real.smoothTransition.zero_of_nonpos ht, zero_mul, hPhiZero]
  · intro t i theta ht
    change A t (q i theta) = A 1 (q i theta)
    by_cases hp : q i theta ∈ Vs
    · simp only [A, if_pos hp, hFOne t _ ht]
    · simp only [A, if_neg hp, sigma,
        Real.smoothTransition.one_of_one_le ht, Real.smoothTransition.one]
  · intro t i theta hp
    exact (hAm t (q i theta) (hqN i theta)).2.2.1 hp
  · intro t i theta hp
    exact (hAm t (q i theta) (hqN i theta)).2.2.2 hp
  · intro t
    rw [hUnion t]
    exact hAe t
  · intro t
    rw [hUnion t]
    exact hAk t
  · intro i hi
    have hp (theta : UnitCircle) : q i theta ∉ Cs :=
      fun hh => disjoint_left.mp hi ⟨theta, rfl⟩ hh
    refine ⟨fun t theta => (hAm t (q i theta) (hqN i theta)).2.2.2
      (fun hh => hp theta (hVsCs hh)), ?_⟩
    intro t
    apply disjoint_left.mpr
    rintro x ⟨theta, rfl⟩ hx
    exact hp theta ((hAm t (q i theta) (hqN i theta)).2.1.mp hx)

end PoincareConjecture.M25.Topology3D
