import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.CollarIsotopy
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Suspension
import Mathlib.Analysis.SpecialFunctions.SmoothTransition



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1




theorem exists_upper_collar_normalization
    (P : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hfix : ∀ p : S1, P p = p)
    {a b : Real} (hab : a < b)
    {U : Set E2} (hU : IsOpen U) (hcircleU : sphere (0 : E2) 1 ⊆ U) :
    ∃ ε : Real, 0 < ε ∧ ε < 1 ∧
      ∃ S : Set E2, IsCompact S ∧ S ⊆ U ∧
      ∃ G : Diffeomorph 𝓘(Real, Real × E2) 𝓘(Real, Real × E2)
          (Real × E2) (Real × E2) ∞,
        (∀ z, (G z).1 = z.1) ∧
        (∀ t x, t ≤ a → G (t, x) = (t, x)) ∧
        (∀ t x, x ∉ S → G (t, x) = (t, x)) ∧
        (∀ t (p : S1), G (t, (p : E2)) = (t, (p : E2))) ∧
        ∀ t x, b ≤ t → |‖x‖ - 1| < ε → G (t, P x) = (t, x) := by
  obtain ⟨ε, hε, hε1, S, hS, hSU, Φ, hΦ0, hΦ, hΦfix, hΦcircle, hΦgerm⟩ :=
    exists_circle_fixing_collar_isotopy_of_diffeomorph P hfix hU hcircleU
  let β : Real → Real := fun t => Real.smoothTransition ((t - a) / (b - a))
  have hβ : ContDiff Real ∞ β :=
    Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
  have hβrange (t : Real) : β t ∈ Icc (0 : Real) 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hβzero (t : Real) (ht : t ≤ a) : β t = 0 :=
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr ht) (sub_pos.mpr hab).le)
  have hβone (t : Real) (ht : b ≤ t) : β t = 1 :=
    Real.smoothTransition.one_of_one_le ((le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith))
  have hΦm : ContMDiff (𝓘(Real, Real).prod (𝓡 2)) (𝓡 2) ∞
      (fun z : Real × E2 => Φ z.1 z.2) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact hΦ.contMDiff
  have hΦi := Poincare.Manifold.contMDiff_diffeomorph_family_symm Φ hΦm
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hΦi
  let G : Diffeomorph 𝓘(Real, Real × E2) 𝓘(Real, Real × E2)
      (Real × E2) (Real × E2) ∞ := {
    toEquiv := {
      toFun := fun z => (z.1, (Φ (β z.1)).symm z.2)
      invFun := fun z => (z.1, Φ (β z.1) z.2)
      left_inv := fun z => by simp
      right_inv := fun z => by simp }
    contMDiff_toFun := (contDiff_fst.prodMk
      (hΦi.contDiff.comp ((hβ.comp contDiff_fst).prodMk contDiff_snd))).contMDiff
    contMDiff_invFun := (contDiff_fst.prodMk
      (hΦ.comp ((hβ.comp contDiff_fst).prodMk contDiff_snd))).contMDiff }
  refine ⟨ε, hε, hε1, S, hS, hSU, G, fun _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro t x ht
    change (t, (Φ (β t)).symm x) = (t, x)
    rw [hβzero t ht]
    congr 1
    apply (Φ 0).injective
    change Φ 0 ((Φ 0).symm x) = Φ 0 x
    rw [(Φ 0).apply_symm_apply, hΦ0]
  · intro t x hx
    change (t, (Φ (β t)).symm x) = (t, x)
    congr 1
    apply (Φ (β t)).injective
    change Φ (β t) ((Φ (β t)).symm x) = Φ (β t) x
    rw [(Φ (β t)).apply_symm_apply, hΦfix _ _ hx]
  · intro t p
    change (t, (Φ (β t)).symm p) = (t, (p : E2))
    congr 1
    apply (Φ (β t)).injective
    change Φ (β t) ((Φ (β t)).symm p) = Φ (β t) p
    rw [(Φ (β t)).apply_symm_apply, hΦcircle _ (hβrange t) p]
  · intro t x ht hx
    change (t, (Φ (β t)).symm (P x)) = (t, x)
    rw [hβone t ht]
    congr 1
    rw [← hΦgerm x hx, (Φ 1).symm_apply_apply]

end Poincare.Manifold.Schoenflies
