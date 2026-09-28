import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneAngularLift
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneSquareCircle
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals

set_option autoImplicit false

open Set Metric Geometry unitInterval

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "J" => Icc (-1 : ℝ) 1
local notation "C8" => AddCircle (4 * (2 : ℝ))

theorem exists_zero_winding_crossing_arc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : Set E} (tau : (J ×ˢ Q) ≃ₜ T) (htau : tau.IsFinitePL)
    (rho : C(J × Q, Q))
    (hminus : ∀ u : Q, rho (⟨-1, by norm_num⟩, u) = u)
    (hplus : ∀ u : Q, rho (⟨1, by norm_num⟩, u) = u) :
    ∃ (m : ℤ) (f : ℝ → E) (ell : C(J, ℝ)),
      FinitePiecewiseAffineOn f J ∧ InjOn f J ∧
      (∀ s : J, f s = tau ⟨((s : ℝ),
        (squareCircle ((-4 * (m : ℝ) * ((s : ℝ) + 1) : ℝ) : C8) : V2)),
          s.property, (squareCircle _).property⟩) ∧
      f (-1) = tau ⟨(-1, (squareCircle (0 : C8) : V2)),
        by norm_num, (squareCircle _).property⟩ ∧
      f 1 = tau ⟨(1, (squareCircle (0 : C8) : V2)),
        by norm_num, (squareCircle _).property⟩ ∧
      ell ⟨-1, by norm_num⟩ = 0 ∧ ell ⟨1, by norm_num⟩ = 0 ∧
      ∀ s : J,
        rho (s, squareCircle ((-4 * (m : ℝ) * ((s : ℝ) + 1) : ℝ) : C8)) =
          squareCircle ((ell s : ℝ) : C8) := by
  let scale : C(I, J) :=
    ⟨fun t => ⟨2 * (t : ℝ) - 1, by
      have ht := t.property
      constructor <;> linarith [ht.1, ht.2]⟩,
      by fun_prop⟩
  let unscale : C(J, I) :=
    ⟨fun s => ⟨((s : ℝ) + 1) / 2, by
      have hs := s.property
      constructor <;> linarith [hs.1, hs.2]⟩,
      by fun_prop⟩
  have hs0 : scale 0 = ⟨-1, by norm_num⟩ := by apply Subtype.ext; norm_num [scale]
  have hs1 : scale 1 = ⟨1, by norm_num⟩ := by apply Subtype.ext; norm_num [scale]
  have hu0 : unscale ⟨-1, by norm_num⟩ = 0 := by
    apply Subtype.ext; norm_num [unscale]
  have hu1 : unscale ⟨1, by norm_num⟩ = 1 := by
    apply Subtype.ext; norm_num [unscale]
  have hsu (s : J) : scale (unscale s) = s := by
    apply Subtype.ext
    change 2 * (((s : ℝ) + 1) / 2) - 1 = (s : ℝ)
    ring
  let rhoQ : C(I × C8, C8) :=
    ⟨fun p => squareCircle.symm (rho (scale p.1, squareCircle p.2)),
      squareCircle.symm.continuous.comp (rho.continuous.comp
        ((scale.continuous.comp continuous_fst).prodMk
          (squareCircle.continuous.comp continuous_snd)))⟩
  have hr0 (u : C8) : rhoQ (0, u) = u := by
    change squareCircle.symm (rho (scale 0, squareCircle u)) = u
    rw [hs0, hminus, squareCircle.symm_apply_apply]
  have hr1 (u : C8) : rhoQ (1, u) = u := by
    change squareCircle.symm (rho (scale 1, squareCircle u)) = u
    rw [hs1, hplus, squareCircle.symm_apply_apply]
  obtain ⟨theta, m, htheta, htheta0, htheta1, _, _⟩ :=
    exists_marked_annulus_angular_lift_period (by norm_num : 0 < 4 * (2 : ℝ))
      rhoQ hr0 hr1
  let alpha : ℝ →ᴬ[ℝ] ℝ := (-4 * (m : ℝ)) •
    (ContinuousAffineMap.id ℝ ℝ + ContinuousAffineMap.const ℝ ℝ 1)
  have ha (s : ℝ) : alpha s = -4 * (m : ℝ) * (s + 1) := rfl
  have ha0 : alpha (-1) = 0 := by rw [ha]; ring
  have ha1 : alpha 1 = -(4 * (2 : ℝ)) * (m : ℝ) := by rw [ha]; ring
  have haperiod : ((alpha 1 : ℝ) : C8) = 0 := by
    rw [ha1]
    apply (AddCircle.coe_eq_zero_iff (4 * (2 : ℝ))).mpr
    refine ⟨-m, ?_⟩
    rw [zsmul_eq_mul, Int.cast_neg]
    ring
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKJ, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)
  have hid : FinitePiecewiseAffineOn (id : ℝ → ℝ) J :=
    ⟨K, hK, hKJ, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)⟩
  have halpha : FinitePiecewiseAffineOn alpha J :=
    ⟨K, hK, hKJ, K.affineOnFaces_affine alpha⟩
  let b : ℝ → ℝ × V2 := fun s => (s, squareCircle ((alpha s : ℝ) : C8))
  have hb : FinitePiecewiseAffineOn b J :=
    hid.prod_mk (finitePiecewiseAffineOn_squareCircle_comp halpha)
  have hbmem (s : J) : b s ∈ J ×ˢ Q :=
    ⟨s.property, (squareCircle _).property⟩
  obtain ⟨F, hF, hFval⟩ := htau
  let f : ℝ → E := F ∘ b
  have hfval (s : J) : f s = (tau ⟨b s, hbmem s⟩ : E) :=
    (hFval ⟨b s, hbmem s⟩).symm
  let ell : C(J, ℝ) :=
    theta.comp (unscale.prodMk
      ⟨fun s => alpha (s : ℝ), alpha.continuous.comp continuous_subtype_val⟩)
  refine ⟨m, f, ell, hF.comp hb (fun s hs => hbmem ⟨s, hs⟩), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs t ht hst
    have htauEq : tau ⟨b s, hbmem ⟨s, hs⟩⟩ = tau ⟨b t, hbmem ⟨t, ht⟩⟩ := by
      apply Subtype.ext
      exact (hfval ⟨s, hs⟩).symm.trans (hst.trans (hfval ⟨t, ht⟩))
    have hbEq := congrArg Subtype.val (tau.injective htauEq)
    exact congrArg Prod.fst hbEq
  · intro s
    exact hfval s
  · rw [hfval ⟨-1, by norm_num⟩]
    change (tau ⟨(-1, (squareCircle ((alpha (-1) : ℝ) : C8) : V2)), _⟩ : E) = _
    simp only [ha0, AddCircle.coe_zero]
  · rw [hfval ⟨1, by norm_num⟩]
    change (tau ⟨(1, (squareCircle ((alpha 1 : ℝ) : C8) : V2)), _⟩ : E) = _
    simp only [haperiod]
  · change theta (unscale ⟨-1, by norm_num⟩, alpha (-1)) = 0
    rw [hu0, ha0, htheta0]
  · change theta (unscale ⟨1, by norm_num⟩, alpha 1) = 0
    rw [hu1, ha1, htheta1]
    ring
  · intro s
    have heq := congrArg squareCircle (htheta (unscale s, alpha s))
    change squareCircle ((ell s : ℝ) : C8) =
      squareCircle (squareCircle.symm (rho (scale (unscale s), squareCircle _))) at heq
    rw [squareCircle.apply_symm_apply, hsu] at heq
    exact heq.symm

end PoincareConjecture.M76.HamiltonIndexOne
