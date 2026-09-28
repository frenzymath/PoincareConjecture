import PoincareConjecture.Proofs.M25.Topology3D.Plane.Tube
import PoincareConjecture.Proofs.M25.Topology3D.Plane.PositiveTubeGraph
import Mathlib.Analysis.Calculus.Deriv.Prod

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

theorem exists_nearby_positive_tube_projection
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : ℂ ≃ₗᵢ[ℝ] E) (q0 : sphere (0 : E) 1)
    (T : OpenPartialHomeomorph (ℝ × E) (ℝ × E))
    (hInv : ContDiffOn ℝ ∞ T.symm T.target)
    (hx : ∀ y ∈ T.target, (T.symm y).2 ≠ 0)
    (γ : ℝ → ℝ → E) (hγ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => γ p.1 p.2))
    (z0 : ℝ) {A : ℝ} (hA : 0 < A)
    (htarget : ∀ s ∈ Icc 0 (2 * Real.pi), (z0, γ z0 s) ∈ T.target)
    (hproj : ∀ s : ℝ, curveTubeProjection q0 T (z0, γ z0 s) = sphereCircleParameter e s)
    (hzero : ∀ s ∈ Icc 0 (2 * Real.pi), curveTubeHeight T (z0, γ z0 s) = 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ z ∈ Ioo (z0 - η) (z0 + η), ∀ s ∈ Icc 0 (2 * Real.pi),
      ((z, s), γ z s) ∈ curveTubeAngularDomain e q0 T ∧
      0 < fderiv ℝ (fun y : E => curveTubeAngle e q0 T ((z, s), y))
        (γ z s) (deriv (γ z) s) ∧ |curveTubeHeight T (z, γ z s)| < A := by
  let C : ℝ × ℝ → E := fun p => γ p.1 p.2
  let d : ℝ × ℝ → E := fun p => fderiv ℝ C p (0, 1)
  have hdcont : Continuous d :=
    ((hγ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have hd (z s : ℝ) : HasDerivAt (γ z) (d (z, s)) s :=
    (hγ.differentiable (by simp) (z, s)).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_const s z).prodMk (hasDerivAt_id s))
  let V := curveTubeAngularDomain e q0 T
  let D : (ℝ × ℝ) × E → E →L[ℝ] ℝ := fun p =>
    fderiv ℝ (fun y : E => curveTubeAngle e q0 T (p.1, y)) p.2
  have hV : IsOpen V := (curveTubeAngle_regular e q0 T hInv hx).1
  have hD : ContinuousOn D V := (contDiffOn_fderiv_curveTubeAngle e q0 T hInv hx).continuousOn
  let B : Set ((ℝ × ℝ) × (E × E)) := {p | (p.1, p.2.1) ∈ V}
  let J : (ℝ × ℝ) × (E × E) → ℝ := fun p => D (p.1, p.2.1) p.2.2
  let H : (ℝ × ℝ) × (E × E) → ℝ := fun p => curveTubeHeight T (p.1.1, p.2.1)
  have hB : IsOpen B := hV.preimage (continuous_fst.prodMk continuous_snd.fst)
  have hJ : ContinuousOn J B :=
    (hD.comp (continuous_fst.prodMk continuous_snd.fst).continuousOn
      (fun _ hp => hp)).clm_apply continuous_snd.snd.continuousOn
  have hH : ContinuousOn H B :=
    (contDiffOn_curveTubeHeight T hInv hx).continuousOn.comp
      (continuous_fst.fst.prodMk continuous_snd.fst).continuousOn (fun _ hp => hp.1)
  let W := B ∩ (fun p => (J p, H p)) ⁻¹' (Ioi (0 : ℝ) ×ˢ Ioo (-A) A)
  have hW : IsOpen W := (hJ.prodMk hH).isOpen_inter_preimage hB (isOpen_Ioi.prod isOpen_Ioo)
  let P : ℝ × ℝ → (ℝ × ℝ) × (E × E) := fun p => (p, (γ p.1 p.2, d p))
  have hP : Continuous P := continuous_id.prodMk (hγ.continuous.prodMk hdcont)
  have hbase : ({z0} : Set ℝ) ×ˢ Icc 0 (2 * Real.pi) ⊆ P ⁻¹' W := by
    rintro ⟨z, s⟩ ⟨hz, hs⟩
    have hzz : z = z0 := hz
    subst z
    have hdom := mem_curveTubeAngularDomain_of_projection e q0 T z0 s s (γ z0 s)
      (htarget s hs) (hproj s) (show s - s ∈ Ioo (-Real.pi) Real.pi by simp [Real.pi_pos])
    refine ⟨hdom, ?_, ?_⟩
    · have hcal := fderiv_curveTubeAngle_apply_velocity e q0 T hInv hx (γ z0) z0 s
        (hd z0 s).differentiableAt (htarget s hs) hproj
      rw [(hd z0 s).deriv] at hcal
      change 0 < D ((z0, s), γ z0 s) (d (z0, s))
      rw [show D ((z0, s), γ z0 s) (d (z0, s)) = 1 from hcal]
      exact zero_lt_one
    · change -A < curveTubeHeight T (z0, γ z0 s) ∧ curveTubeHeight T (z0, γ z0 s) < A
      rw [hzero s hs]
      exact ⟨neg_neg_of_pos hA, hA⟩
  obtain ⟨U, S, hU, _, hzU, hsS, hUS⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc (hW.preimage hP) hbase
  obtain ⟨η, hη, hηU⟩ := exists_interval_margin (a := z0) (b := z0) le_rfl hU
    (by simpa only [Icc_self] using hzU)
  refine ⟨η, hη, ?_⟩
  intro z hz s hs
  have hmem : P (z, s) ∈ W := hUS (show (z, s) ∈ U ×ˢ S from ⟨hηU hz, hsS hs⟩)
  refine ⟨hmem.1, ?_, abs_lt.mpr hmem.2.2⟩
  rw [(hd z s).deriv]
  exact hmem.2.1

theorem exists_nearby_curve_transport
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)]
    (e : ℂ ≃ₗᵢ[ℝ] E) (o : Orientation ℝ E (Fin 2)) (q0 : sphere (0 : E) 1)
    (c : ℝ → sphere (0 : E) 1 → E)
    (hc : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × sphere (0 : E) 1 => c p.1 p.2))
    (z0 : ℝ) (hi : Injective (c z0))
    (hm : ∀ q : sphere (0 : E) 1, Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) (c z0) q)) :
    ∃ r : ℝ, 0 < r ∧ ∃ F : ℝ → (E ≃ₘ[ℝ] E),
      ContDiff ℝ ∞ (fun p : ℝ × E => F p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => (F p.1).symm p.2) ∧
      (∃ Q : Set E, IsCompact Q ∧ ∀ z x, x ∉ Q → F z x = x ∧ (F z).symm x = x) ∧
      (∀ z, HasCompactSupport (fun x => F z x - x) ∧
        HasCompactSupport (fun x => (F z).symm x - x)) ∧
      (∀ x, F z0 x = x) ∧ ∀ z ∈ Icc (z0 - r) (z0 + r),
        range (fun q : sphere (0 : E) 1 => F z (c z0 q)) = range (c z) := by
  let c0 : ℝ → sphere (0 : E) 1 → E := fun _ q => c z0 q
  have hc0 : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × sphere (0 : E) 1 => c0 p.1 p.2) :=
    hc.comp (contMDiff_const.prodMk contMDiff_snd)
  obtain ⟨m, hm0, w, hw0, hw1, T, hs, he, hfwd, hInv⟩ := exists_curveAnnularTube o q0 c0 hc0
    (a := z0) (b := z0) le_rfl (fun _ _ => hi) (fun _ _ => hm)
  have hx (y : ℝ × E) (hy : y ∈ T.target) : (T.symm y).2 ≠ 0 :=
    (curveAnnularTube_coordinates o q0 c0 T hw1 hs he hy).1
  have hcoords (q : sphere (0 : E) 1) :
      (z0, c z0 q) ∈ T.target ∧ curveTubeProjection q0 T (z0, c z0 q) = q ∧
        curveTubeHeight T (z0, c z0 q) = 0 := by
    simpa only [c0, zero_smul, add_zero] using
      curveAnnularTube_coordinates_apply o q0 c0 T hw1 hs he
      z0 (show z0 ∈ Ioo (z0 - m) (z0 + m) by constructor <;> linarith) q
      (r := 0) (by simpa only [abs_zero] using hw0)
  let γ : ℝ → ℝ → E := fun z s => c z (sphereCircleParameter e s)
  have hγ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => γ p.1 p.2) :=
    contDiff_curveFamily_circleParameter e c hc
  have hγper (z : ℝ) : Periodic (γ z) (2 * Real.pi) := by
    intro s
    exact congrArg (c z) (periodic_sphereCircleParameter e s)
  have hA : 0 < w / 2 := half_pos hw0
  obtain ⟨η, hη, hnear⟩ := exists_nearby_positive_tube_projection e q0 T hInv hx γ hγ z0 hA
    (fun s _ => (hcoords (sphereCircleParameter e s)).1)
    (fun s => (hcoords (sphereCircleParameter e s)).2.1)
    (fun s _ => (hcoords (sphereCircleParameter e s)).2.2)
  let r := min η m / 4
  have hr : 0 < r := div_pos (lt_min hη hm0) (by norm_num)
  have hrη : 2 * r ≤ η := by
    dsimp [r]
    linarith [min_le_left η m]
  have hrm : 2 * r ≤ m := by
    dsimp [r]
    linarith [min_le_right η m]
  have hgood {z : ℝ} (hz : z ∈ Ioo (z0 - 2 * r) (z0 + 2 * r)) :
      z ∈ Ioo (z0 - η) (z0 + η) := ⟨by linarith [hz.1], by linarith [hz.2]⟩
  obtain ⟨D, hD, hDinv, ⟨Q, hQ, hfix⟩, _, hDrange⟩ := exists_positive_tube_curve_transport
    e o q0 c0 T hw1 hs he hfwd hInv (L := z0 - 2 * r) (U := z0 + 2 * r)
    (a := z0 - r) (b := z0 + r) (by linarith) (by linarith) (by linarith) (by linarith)
    hA (by linarith) γ hγ hγper
    (fun z hz s hst => (hnear z (hgood hz) s hst).1)
    (fun z hz s hst => (hnear z (hgood hz) s hst).2.1)
    (fun z hz s hst => (hnear z (hgood hz) s hst).2.2)
  have hγrange (z : ℝ) : range (γ z) = range (c z) := by
    apply Subset.antisymm
    · rintro y ⟨s, rfl⟩
      exact ⟨sphereCircleParameter e s, rfl⟩
    · rintro y ⟨q, rfl⟩
      obtain ⟨s, rfl⟩ := surjective_sphereCircleParameter e q
      exact ⟨s, rfl⟩
  have hrange (z : ℝ) (hz : z ∈ Icc (z0 - r) (z0 + r)) :
      D z '' range (c z0) = range (c z) := by
    rw [← range_comp']
    exact (hDrange z hz).trans (hγrange z)
  have hz0 : z0 ∈ Icc (z0 - r) (z0 + r) := ⟨by linarith, by linarith⟩
  have hinvrange : (D z0).symm '' range (c z0) = range (c z0) := by
    nth_rw 1 [← hrange z0 hz0]
    rw [image_image]
    simp only [Diffeomorph.symm_apply_apply, image_id']
  let F : ℝ → (E ≃ₘ[ℝ] E) := fun z => (D z0).symm.trans (D z)
  have hF : ContDiff ℝ ∞ (fun p : ℝ × E => F p.1 p.2) :=
    hD.comp (contDiff_fst.prodMk ((D z0).symm.contDiff.comp contDiff_snd))
  have hFinv : ContDiff ℝ ∞ (fun p : ℝ × E => (F p.1).symm p.2) :=
    (D z0).contDiff.comp hDinv
  have hFfix (z : ℝ) (x : E) (hxQ : x ∉ Q) : F z x = x ∧ (F z).symm x = x := by
    change D z ((D z0).symm x) = x ∧ D z0 ((D z).symm x) = x
    rw [(hfix z0 x hxQ).2, (hfix z x hxQ).1, (hfix z x hxQ).2, (hfix z0 x hxQ).1]
    exact ⟨rfl, rfl⟩
  refine ⟨r, hr, F, hF, hFinv, ⟨Q, hQ, hFfix⟩, ?_, ?_, ?_⟩
  · intro z
    exact ⟨HasCompactSupport.intro hQ (fun x hxQ => sub_eq_zero.mpr (hFfix z x hxQ).1),
      HasCompactSupport.intro hQ (fun x hxQ => sub_eq_zero.mpr (hFfix z x hxQ).2)⟩
  · intro x
    exact (D z0).apply_symm_apply x
  · intro z hz
    change range (fun q : sphere (0 : E) 1 => D z ((D z0).symm (c z0 q))) = range (c z)
    rw [range_comp', range_comp', hinvrange]
    exact hrange z hz

end PoincareConjecture.M25.Topology3D
