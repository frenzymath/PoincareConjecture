import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.CollarSuspension
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Circle.BoundaryReparametrization
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Circle.RadialGerm



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1





theorem exists_upper_boundary_alignment_of_planar_fillings
    (γ : S1 → E2) (hγ : _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ γ)
    (A B : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hA : A '' sphere (0 : E2) 1 = range γ)
    (hB : B '' sphere (0 : E2) 1 = range γ)
    {a b : Real} (hab : a < b) :
    ∃ q : Diffeomorph (𝓡 1) (𝓡 1) S1 S1 ∞,
      (∀ p : S1, B (q p : E2) = A p) ∧
      ∃ ε : Real, 0 < ε ∧ ε < 1 ∧
        ∃ S : Set E2, IsCompact S ∧
        ∃ G : Diffeomorph 𝓘(Real, Real × E2) 𝓘(Real, Real × E2)
            (Real × E2) (Real × E2) ∞,
          (∀ z, (G z).1 = z.1) ∧
          (∀ t x, t ≤ a → G (t, x) = (t, x)) ∧
          (∀ t x, x ∉ S → G (t, x) = (t, x)) ∧
          (∀ t p, G (t, γ p) = (t, γ p)) ∧
          ∀ t (p : S1) ρ, b ≤ t → |ρ - 1| < ε →
            G (t, B (ρ • (q p : E2))) = (t, A (ρ • (p : E2))) := by
  obtain ⟨qA, hqA⟩ := exists_planar_boundary_reparametrization γ hγ A hA
  obtain ⟨qB, hqB⟩ := exists_planar_boundary_reparametrization γ hγ B hB
  let q := qA.symm.trans qB
  have hq (p : S1) : B (q p : E2) = A p := by
    change B (qB (qA.symm p) : E2) = A p
    rw [hqB, ← hqA, qA.apply_symm_apply]
  obtain ⟨H, _, _, η, hη, hη1, hH⟩ :=
    exists_radial_ambient_diffeomorph_of_circle_diffeomorph q
  let P := (H.trans B).trans A.symm
  have hPfix (p : S1) : P p = (p : E2) := by
    change A.symm (B (H p)) = (p : E2)
    have hHp : H p = (q p : E2) := by simpa using hH p 1 (by simpa using hη)
    rw [hHp, hq, A.symm_apply_apply]
  obtain ⟨ζ, hζ, hζ1, K, hK, _, D, hDheight, hDlower, hDsupport, hDcylinder, hDgerm⟩ :=
    exists_upper_collar_normalization P hPfix hab isOpen_univ (subset_univ _)
  let C : Diffeomorph 𝓘(Real, Real × E2) 𝓘(Real, Real × E2)
      (Real × E2) (Real × E2) ∞ := {
    toEquiv := (Equiv.refl Real).prodCongr A.toEquiv
    contMDiff_toFun := (contDiff_fst.prodMk (A.contDiff.comp contDiff_snd)).contMDiff
    contMDiff_invFun := (contDiff_fst.prodMk (A.symm.contDiff.comp contDiff_snd)).contMDiff }
  let G := (C.symm.trans D).trans C
  let ε := min η ζ
  have hε : 0 < ε := lt_min hη hζ
  have hεη : ε ≤ η := min_le_left _ _
  have hεζ : ε ≤ ζ := min_le_right _ _
  have hε1 : ε < 1 := hεη.trans_lt hη1
  refine ⟨q, hq, ε, hε, hε1, A '' K, hK.image A.contMDiff.continuous,
    G, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    change (D (C.symm z)).1 = z.1
    rw [hDheight]
    rfl
  · intro t x ht
    change C (D (t, A.symm x)) = (t, x)
    rw [hDlower t (A.symm x) ht]
    change (t, A (A.symm x)) = (t, x)
    rw [A.apply_symm_apply]
  · intro t x hx
    have hxK : A.symm x ∉ K := fun h => hx ⟨A.symm x, h, A.apply_symm_apply x⟩
    change C (D (t, A.symm x)) = (t, x)
    rw [hDsupport t (A.symm x) hxK]
    change (t, A (A.symm x)) = (t, x)
    rw [A.apply_symm_apply]
  · intro t p
    rw [← hqA p]
    change C (D (t, A.symm (A (qA p)))) = (t, A (qA p))
    rw [A.symm_apply_apply, hDcylinder t (qA p)]
    rfl
  · intro t p ρ ht hρ
    have hρη : |ρ - 1| < η := hρ.trans_le hεη
    have hρpos : 0 < ρ := by have := (abs_lt.mp (hρ.trans hε1)).1; linarith
    have hx : |‖ρ • (p : E2)‖ - 1| < ζ := by
      simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hρpos] using hρ.trans_le hεζ
    change C (D (t, A.symm (B (ρ • (q p : E2))))) = _
    rw [← hH p ρ hρη]
    change C (D (t, P (ρ • (p : E2)))) = _
    rw [hDgerm t _ ht hx]
    rfl

end Poincare.Manifold.Schoenflies
