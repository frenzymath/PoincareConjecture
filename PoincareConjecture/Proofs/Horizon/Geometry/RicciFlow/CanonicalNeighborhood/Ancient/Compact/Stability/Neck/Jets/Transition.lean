import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.TransitionBounds













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff Topology

namespace PoincareConjecture.CoordinateTransition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem hasUniformJetBoundsOn_of_christoffel_hessian_finite
    {ι : Type*} {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {f : ι → E → E} {A B : ι → E → E →L[ℝ] E →L[ℝ] E}
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) U)
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) U)
    (hB : ∀ i, ContDiffOn ℝ ∞ (B i) V)
    (hmap : ∀ i, MapsTo (f i) U V)
    {m : ℕ} (hAj : HasUniformJetBoundsOn m U A)
    (hBj : HasUniformJetBoundsOn m V B)
    (hzero : ∃ C : ℝ, ∀ i x, x ∈ U → ‖f i x‖ ≤ C)
    (hfirst : ∃ C : ℝ, ∀ i x, x ∈ U → ‖fderiv ℝ (f i) x‖ ≤ C)
    (hEq : ∀ i x, x ∈ U → ∀ u v,
      fderiv ℝ (fderiv ℝ (f i)) x u v =
        fderiv ℝ (f i) x (A i x u v) -
          B i (f i x) (fderiv ℝ (f i) x u) (fderiv ℝ (f i) x v)) :
    HasUniformJetBoundsOn (m + 2) U f := by
  let D := fun i => fderiv ℝ (f i)
  have hD : ∀ i, ContDiffOn ℝ ∞ (D i) U :=
    fun i => (hf i).fderiv_of_isOpen hU (by simp)
  have hBc : ∀ i, ContDiffOn ℝ ∞ (fun x => B i (f i x)) U :=
    fun i => (hB i).comp (hf i) (hmap i)
  let flipL := (ContinuousLinearMap.flipₗᵢ ℝ E E E).toLinearIsometry.toContinuousLinearMap
  have hDj : ∀ n, n ≤ m + 1 → HasUniformJetBoundsOn n U D := by
    intro n
    induction n with
    | zero =>
        intro _ r hr
        have : r = 0 := Nat.eq_zero_of_le_zero hr
        subst r
        simpa only [norm_iteratedFDeriv_zero] using hfirst
    | succ n ih =>
        intro hn
        have hnm : n ≤ m := by omega
        have ih := ih (by omega)
        have hfj : HasUniformJetBoundsOn n U f :=
          (HasUniformJetBoundsOn.succ_of_fderiv hzero ih).mono_order (Nat.le_succ n)
        have hBfj : HasUniformJetBoundsOn n U (fun i x => B i (f i x)) :=
          hfj.comp hU hV (hBj.mono_order hnm)
            (fun i => (hf i).of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))
            (fun i => (hB i).of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))) hmap
        have hpost := ih.clm hU hD (ContinuousLinearMap.compL ℝ E E E)
        have hcpost : ∀ i, ContDiffOn ℝ ∞
            (fun x => ContinuousLinearMap.compL ℝ E E E (D i x)) U :=
          fun i => (ContinuousLinearMap.compL ℝ E E E).contDiff.comp_contDiffOn (hD i)
        have hleft := hpost.clm_comp hU (hAj.mono_order hnm) hcpost hA
        have hpre := hBfj.clm_comp hU ih hBc hD
        have hcpre : ∀ i, ContDiffOn ℝ ∞ (fun x => (B i (f i x)).comp (D i x)) U :=
          fun i => (hBc i).clm_comp (hD i)
        have hflip := hpre.clm hU hcpre flipL
        have hcflip : ∀ i, ContDiffOn ℝ ∞
            (fun x => flipL ((B i (f i x)).comp (D i x))) U :=
          fun i => flipL.contDiff.comp_contDiffOn (hcpre i)
        have hpre' := hflip.clm_comp hU ih hcflip hD
        have hcpre' : ∀ i, ContDiffOn ℝ ∞
            (fun x => (flipL ((B i (f i x)).comp (D i x))).comp (D i x)) U :=
          fun i => (hcflip i).clm_comp (hD i)
        have hright := hpre'.clm hU hcpre' flipL
        have hcleft : ∀ i, ContDiffOn ℝ ∞
            (fun x => (ContinuousLinearMap.compL ℝ E E E (D i x)).comp (A i x)) U :=
          fun i => (hcpost i).clm_comp (hA i)
        have hcright : ∀ i, ContDiffOn ℝ ∞
            (fun x => flipL ((flipL ((B i (f i x)).comp (D i x))).comp (D i x))) U :=
          fun i => flipL.contDiff.comp_contDiffOn (hcpre' i)
        apply HasUniformJetBoundsOn.succ_of_fderiv hfirst
        apply (hleft.sub hU hright hcleft hcright).congr hU
        intro i x hx
        ext u v
        exact (hEq i x hx u v).symm
  exact HasUniformJetBoundsOn.succ_of_fderiv hzero (hDj (m + 1) le_rfl)

end PoincareConjecture.CoordinateTransition
