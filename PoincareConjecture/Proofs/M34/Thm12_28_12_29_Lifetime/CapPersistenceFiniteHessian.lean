import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.TransitionBounds

set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareConjecture.CoordinateTransition

theorem hasUniformJetBoundsOn_of_finite_christoffel_hessian
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {f : ι → E → E} {A B : ι → E → E →L[ℝ] E →L[ℝ] E}
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) U)
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) U)
    (hB : ∀ i, ContDiffOn ℝ ∞ (B i) V)
    (hmap : ∀ i, MapsTo (f i) U V)
    (hAj : HasUniformJetBoundsOn n U A)
    (hBj : HasUniformJetBoundsOn n V B)
    (hzero : ∃ C : ℝ, ∀ i x, x ∈ U → ‖f i x‖ ≤ C)
    (hfirst : ∃ C : ℝ, ∀ i x, x ∈ U → ‖fderiv ℝ (f i) x‖ ≤ C)
    (hEq : ∀ i x, x ∈ U → ∀ u v,
      fderiv ℝ (fderiv ℝ (f i)) x u v =
        fderiv ℝ (f i) x (A i x u v) -
          B i (f i x) (fderiv ℝ (f i) x u) (fderiv ℝ (f i) x v)) :
    HasUniformJetBoundsOn (n + 2) U f := by
  let D := fun i => fderiv ℝ (f i)
  have hD : ∀ i, ContDiffOn ℝ ∞ (D i) U :=
    fun i => (hf i).fderiv_of_isOpen hU (by simp)
  have hBc : ∀ i, ContDiffOn ℝ ∞ (fun x => B i (f i x)) U :=
    fun i => (hB i).comp (hf i) (hmap i)
  let flipL := (ContinuousLinearMap.flipₗᵢ ℝ E E E).toLinearIsometry.toContinuousLinearMap
  have hDj : ∀ m, m ≤ n + 1 → HasUniformJetBoundsOn m U D := by
    intro m
    induction m with
    | zero =>
        intro _ j hj
        have : j = 0 := Nat.eq_zero_of_le_zero hj
        subst j
        simpa only [norm_iteratedFDeriv_zero] using hfirst
    | succ m ih =>
        intro hm
        have hmn : m ≤ n := Nat.le_of_succ_le_succ hm
        have hprev := ih (by omega)
        have hfj : HasUniformJetBoundsOn m U f :=
          (HasUniformJetBoundsOn.succ_of_fderiv hzero hprev).mono_order (Nat.le_succ m)
        have hBfj : HasUniformJetBoundsOn m U (fun i x => B i (f i x)) :=
          hfj.comp hU hV (hBj.mono_order hmn)
            (fun i => (hf i).of_le (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤)))
            (fun i => (hB i).of_le (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤))) hmap
        have hpost := hprev.clm hU hD (ContinuousLinearMap.compL ℝ E E E)
        have hcpost : ∀ i, ContDiffOn ℝ ∞
            (fun x => ContinuousLinearMap.compL ℝ E E E (D i x)) U :=
          fun i => (ContinuousLinearMap.compL ℝ E E E).contDiff.comp_contDiffOn (hD i)
        have hleft := hpost.clm_comp hU (hAj.mono_order hmn) hcpost hA
        have hpre := hBfj.clm_comp hU hprev hBc hD
        have hcpre : ∀ i, ContDiffOn ℝ ∞ (fun x => (B i (f i x)).comp (D i x)) U :=
          fun i => (hBc i).clm_comp (hD i)
        have hflip := hpre.clm hU hcpre flipL
        have hcflip : ∀ i, ContDiffOn ℝ ∞
            (fun x => flipL ((B i (f i x)).comp (D i x))) U :=
          fun i => flipL.contDiff.comp_contDiffOn (hcpre i)
        have hpre' := hflip.clm_comp hU hprev hcflip hD
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
  exact HasUniformJetBoundsOn.succ_of_fderiv hzero (hDj (n + 1) le_rfl)

end PoincareConjecture.CoordinateTransition
