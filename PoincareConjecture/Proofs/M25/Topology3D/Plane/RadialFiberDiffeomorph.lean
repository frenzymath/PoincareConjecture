import PoincareConjecture.Proofs.M25.Topology3D.Plane.RadialFiber
import Mathlib.Geometry.Manifold.Diffeomorph










set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D



theorem exists_radialFiberDiffeomorph
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : ((ℝ × E) × ℝ) ≃ₘ[ℝ] ((ℝ × E) × ℝ))
    (hparam : ∀ p, (D p).1 = p.1) {w : ℝ} (hw : w < 1)
    (hmono : ∀ u : ℝ × E, StrictMono (fun r : ℝ => (D (u, r)).2))
    (hfix : ∀ p : (ℝ × E) × ℝ, w ≤ |p.2| → D p = p) :
    ∃ A : (ℝ × E) ≃ₘ[ℝ] (ℝ × E),
      (∀ p, A p = radialFiberMap (fun v => (D v).2) p) ∧
      (∀ p, A.symm p = radialFiberMap (fun v => (D.symm v).2) p) ∧
      (∀ p, w ≤ |‖p.2‖ - 1| → A p = p) ∧
      (∀ p, (A p).1 = p.1 ∧ (A.symm p).1 = p.1) := by
  let F : (ℝ × E) × ℝ → ℝ := fun p => (D p).2
  let G : (ℝ × E) × ℝ → ℝ := fun p => (D.symm p).2
  have hInvparam (p : (ℝ × E) × ℝ) : (D.symm p).1 = p.1 := by
    simpa only [D.apply_symm_apply] using (hparam (D.symm p)).symm
  have hD (u : ℝ × E) (r : ℝ) : D (u, r) = (u, F (u, r)) :=
    Prod.ext (hparam (u, r)) rfl
  have hG (u : ℝ × E) (r : ℝ) : D.symm (u, r) = (u, G (u, r)) :=
    Prod.ext (hInvparam (u, r)) rfl
  have hleft (u : ℝ × E) (r : ℝ) : G (u, F (u, r)) = r := by
    have h := congrArg Prod.snd (D.symm_apply_apply (u, r))
    rw [hD] at h
    exact h
  have hright (u : ℝ × E) (r : ℝ) : F (u, G (u, r)) = r := by
    have h := congrArg Prod.snd (D.apply_symm_apply (u, r))
    rw [hG] at h
    exact h
  have hFfix (p : (ℝ × E) × ℝ) (hp : w ≤ |p.2|) : F p = p.2 :=
    congrArg Prod.snd (hfix p hp)
  have hGfix (p : (ℝ × E) × ℝ) (hp : w ≤ |p.2|) : G p = p.2 := by
    have h := congrArg D.symm (hfix p hp)
    simpa only [D.symm_apply_apply] using (congrArg Prod.snd h).symm
  have hminus (u : ℝ × E) : F (u, -1) = -1 :=
    hFfix (u, -1) (by simpa using hw.le)
  have hFpos (u : ℝ × E) (r : ℝ) (hr : -1 < r) : -1 < F (u, r) := by
    have h := hmono u hr
    change F (u, -1) < F (u, r) at h
    rwa [hminus] at h
  have hGpos (u : ℝ × E) (r : ℝ) (hr : -1 < r) : -1 < G (u, r) := by
    by_contra hn
    have h := (hmono u).monotone (le_of_not_gt hn)
    change F (u, G (u, r)) ≤ F (u, -1) at h
    rw [hright, hminus] at h
    exact (not_le_of_gt hr) h
  have hleftRad : LeftInverse (radialFiberMap G) (radialFiberMap F) :=
    radialFiberMap_leftInverse F G (fun z q _ r _ => hleft (z, q) r)
      (fun z q _ r hr => hFpos (z, q) r hr)
  have hrightRad : LeftInverse (radialFiberMap F) (radialFiberMap G) :=
    radialFiberMap_leftInverse G F (fun z q _ r _ => hright (z, q) r)
      (fun z q _ r hr => hGpos (z, q) r hr)
  let A : (ℝ × E) ≃ₘ[ℝ] (ℝ × E) :=
    { toEquiv :=
        { toFun := radialFiberMap F
          invFun := radialFiberMap G
          left_inv := hleftRad
          right_inv := hrightRad }
      contMDiff_toFun := (contDiff_radialFiberMap F D.contDiff.snd hw hFfix).contMDiff
      contMDiff_invFun := (contDiff_radialFiberMap G D.symm.contDiff.snd hw hGfix).contMDiff }
  refine ⟨A, (fun _ => rfl), (fun _ => rfl), ?_, ?_⟩
  · intro p hp
    exact radialFiberMap_eq_self F p (hFfix _ hp)
  · intro p
    exact ⟨rfl, rfl⟩

end PoincareConjecture.M25.Topology3D
