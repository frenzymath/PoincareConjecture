import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.BoundaryAlignment



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1




theorem exists_upper_boundary_alignment_with_constant_endpoint
    (γ : S1 → E2)
    (hγ : _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ γ)
    (A B : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hA : A '' sphere (0 : E2) 1 = range γ)
    (hB : B '' sphere (0 : E2) 1 = range γ)
    {a b : Real} (hab : a < b) :
    ∃ q : Diffeomorph (𝓡 1) (𝓡 1) S1 S1 ∞,
      (∀ p : S1, B (q p) = A p) ∧
      ∃ ε : Real, 0 < ε ∧ ε < 1 ∧
        ∃ Q : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
          ∃ G : Diffeomorph 𝓘(Real, Real × E2) 𝓘(Real, Real × E2)
              (Real × E2) (Real × E2) ∞,
            (∀ z, (G z).1 = z.1) ∧
            (∀ t x, t ≤ a → G (t, x) = (t, x)) ∧
            (∀ (t : Real) (p : S1), G (t, γ p) = (t, γ p)) ∧
            (∀ t x, b ≤ t → G (t, x) = (t, Q x)) ∧
            ∀ (p : S1) (ρ : Real), |ρ - 1| < ε →
              Q (B (ρ • (q p : E2))) = A (ρ • (p : E2)) := by
  obtain ⟨q, hq, ε, hε, hε1, K, hK, G₀, hG₀first, hG₀lower, hG₀fix,
    hG₀circle, hG₀germ⟩ :=
    exists_upper_boundary_alignment_of_planar_fillings γ hγ A B hA hB hab
  have hG₀ifirst (z : Real × E2) : (G₀.symm z).1 = z.1 := by
    rw [← hG₀first (G₀.symm z), G₀.apply_symm_apply]
  let Φ (t : Real) : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ := {
    toEquiv := {
      toFun := fun x => (G₀ (t, x)).2
      invFun := fun x => (G₀.symm (t, x)).2
      left_inv := fun x => by
        change (G₀.symm (t, (G₀ (t, x)).2)).2 = x
        have he : (t, (G₀ (t, x)).2) = G₀ (t, x) :=
          Prod.ext (hG₀first (t, x)).symm rfl
        rw [he, G₀.symm_apply_apply]
      right_inv := fun x => by
        change (G₀ (t, (G₀.symm (t, x)).2)).2 = x
        have he : (t, (G₀.symm (t, x)).2) = G₀.symm (t, x) :=
          Prod.ext (hG₀ifirst (t, x)).symm rfl
        rw [he, G₀.apply_symm_apply] }
    contMDiff_toFun := (contDiff_snd.comp
      (G₀.contMDiff.contDiff.comp (contDiff_const.prodMk contDiff_id))).contMDiff
    contMDiff_invFun := (contDiff_snd.comp
      (G₀.symm.contMDiff.contDiff.comp (contDiff_const.prodMk contDiff_id))).contMDiff }
  let θ : Real → Real := fun t => a + (b - a) * Real.smoothTransition ((t - a) / (b - a))
  have hθ : ContDiff Real ∞ θ := contDiff_const.add
    (contDiff_const.mul (Real.smoothTransition.contDiff.comp
      ((contDiff_id.sub contDiff_const).div_const _)))
  have hθa (t : Real) (ht : t ≤ a) : θ t = a := by
    have h := Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_pos.mpr hab).le)
    simp [θ, h]
  have hθb (t : Real) (ht : b ≤ t) : θ t = b := by
    have h : Real.smoothTransition ((t - a) / (b - a)) = 1 := Real.smoothTransition.one_of_one_le
      ((le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith))
    simp [θ, h]
  let G : Diffeomorph 𝓘(Real, Real × E2) 𝓘(Real, Real × E2)
      (Real × E2) (Real × E2) ∞ := {
    toEquiv := {
      toFun := fun z => (z.1, Φ (θ z.1) z.2)
      invFun := fun z => (z.1, (Φ (θ z.1)).symm z.2)
      left_inv := fun z => by simp
      right_inv := fun z => by simp }
    contMDiff_toFun := (contDiff_fst.prodMk (contDiff_snd.comp
      (G₀.contMDiff.contDiff.comp ((hθ.comp contDiff_fst).prodMk contDiff_snd)))).contMDiff
    contMDiff_invFun := (contDiff_fst.prodMk (contDiff_snd.comp
      (G₀.symm.contMDiff.contDiff.comp ((hθ.comp contDiff_fst).prodMk contDiff_snd)))).contMDiff }
  refine ⟨q, hq, ε, hε, hε1, Φ b, G, fun _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro t x ht
    change (t, (G₀ (θ t, x)).2) = (t, x)
    rw [hθa t ht, hG₀lower a x le_rfl]
  · intro t p
    change (t, (G₀ (θ t, γ p)).2) = (t, γ p)
    rw [hG₀circle]
  · intro t x ht
    change (t, Φ (θ t) x) = (t, Φ b x)
    rw [hθb t ht]
  · intro p ρ hρ
    exact congrArg Prod.snd (hG₀germ b p ρ le_rfl hρ)

end Poincare.Manifold.Schoenflies
