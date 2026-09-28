import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.PotentialLimit.CoefficientBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.Jacobi.Coefficients
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.Pullback

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 1600000

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Q" => E →L[ℝ] ℝ
local notation "T" => E →L[ℝ] Q

local instance : NormedAddCommGroup Q := inferInstance
local instance : NormedSpace ℝ Q := inferInstance
local instance : NormedAddCommGroup T := inferInstance
local instance : NormedSpace ℝ T := inferInstance
local instance : NormedAddCommGroup (E →L[ℝ] T) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] T) := inferInstance
local instance : NormedAddCommGroup (Q →L[ℝ] T) := inferInstance
local instance : NormedSpace ℝ (Q →L[ℝ] T) := inferInstance

def potentialConnectionOperator (J : T × (E →L[ℝ] T)) : Q →L[ℝ] T :=
  let flipL := (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toLinearIsometry.toContinuousLinearMap
  let K := (2⁻¹ : ℝ) • (J.2 + (flipL.comp J.2).flip - flipL.comp J.2.flip)
  let Γ := (ContinuousLinearMap.compL ℝ E Q E J.1.inverse).comp K
  ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] E) Q).flip Γ).comp
    (ContinuousLinearMap.compL ℝ E E ℝ)

theorem potentialConnectionOperator_apply
    (B : E → T) (x : E) (a : Q) (v w : E) :
    potentialConnectionOperator (B x, fderiv ℝ B x) a v w =
      a (CoordinateExponential.christoffelBilinear B x v w) := by
  rfl

theorem contDiffOn_potentialConnectionOperator :
    ContDiffOn ℝ ∞ (potentialConnectionOperator (n := n))
      {J : T × (E →L[ℝ] T) | J.1.IsInvertible} := by
  intro J hJ
  apply ContDiffAt.contDiffWithinAt
  have hi : ContDiffAt ℝ ∞ (fun K : T × (E →L[ℝ] T) => K.1.inverse) J :=
    hJ.contDiffAt_map_inverse.comp J contDiffAt_fst
  have hf : ContDiff ℝ ∞ (fun A : T => A.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).contDiff
  have hf' : ContDiff ℝ ∞ (fun A : E →L[ℝ] T => A.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E Q).contDiff
  let flipL := (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toLinearIsometry.toContinuousLinearMap
  let K := fun J : T × (E →L[ℝ] T) =>
    (2⁻¹ : ℝ) • (J.2 + (flipL.comp J.2).flip - flipL.comp J.2.flip)
  have hK : ContDiffAt ℝ ∞ K J := by
    exact ((contDiffAt_snd.add
      (hf'.contDiffAt.comp J (contDiffAt_const.clm_comp contDiffAt_snd))).sub
        (contDiffAt_const.clm_comp (hf'.contDiffAt.comp J contDiffAt_snd))).const_smul _
  have hc := (ContinuousLinearMap.compL ℝ E Q E).contDiff.contDiffAt.comp J hi
  have hΓ := hc.clm_comp hK
  exact (((ContinuousLinearMap.compL ℝ E (E →L[ℝ] E) Q).flip).contDiff.contDiffAt.comp J hΓ).clm_comp
    contDiffAt_const

open Poincare.Analysis.Calculus

theorem locallyEventuallyBoundedDerivatives_potentialConnectionOperator
    {Ω : Set E} (hΩ : IsOpen Ω) {B : ℕ → E → T} {B₀ : E → T}
    (hs : LocallyEventuallyContDiff Ω B) (hB₀ : ContDiffOn ℝ ∞ B₀ Ω)
    (hi : ∀ x ∈ Ω, (B₀ x).IsInvertible)
    (hjet : ∀ m K, IsCompact K → K ⊆ Ω → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (B k)) (iteratedFDeriv ℝ m B₀) atTop K) :
    LocallyEventuallyContDiff Ω
      (fun k x => potentialConnectionOperator (B k x, fderiv ℝ (B k) x)) ∧
    LocallyEventuallyBoundedDerivatives Ω
      (fun k x => potentialConnectionOperator (B k x, fderiv ℝ (B k) x)) := by
  have hb := locallyEventuallyBoundedDerivatives_of_tendsto_jets hΩ hB₀ hjet
  have hpair := hs.prodMk hs.fderiv
  have hpairbound := hb.prodMk hb.fderiv hs hs.fderiv
  have hpair₀ : ContDiffOn ℝ ∞ (fun x => (B₀ x, fderiv ℝ B₀ x)) Ω :=
    hB₀.prodMk (hB₀.fderiv_of_isOpen hΩ (by simp))
  have hpairconv (K : Set E) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
      TendstoUniformlyOn (fun k x => (B k x, fderiv ℝ (B k) x))
        (fun x => (B₀ x, fderiv ℝ B₀ x)) atTop K := by
    have hv := tendstoUniformlyOn_of_zeroJet (hjet 0 K hK hKΩ)
    have hd := tendstoUniformlyOn_of_zeroJet
      (tendstoUniformlyOn_fderiv_jets 0 (hjet 1 K hK hKΩ))
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hv ε hε,
      Metric.tendstoUniformlyOn_iff.mp hd ε hε] with k hkv hkd x hx
    rw [Prod.dist_eq]
    exact max_lt (hkv x hx) (hkd x hx)
  have hU : IsOpen {J : T × (E →L[ℝ] T) | J.1.IsInvertible} :=
    ContinuousLinearEquiv.isOpen.preimage continuous_fst
  have hmap : MapsTo (fun x => (B₀ x, fderiv ℝ B₀ x)) Ω
      {J : T × (E →L[ℝ] T) | J.1.IsInvertible} := fun _ hx => hi _ hx
  constructor
  · exact LocallyEventuallyContDiff.comp_smooth
      (f := fun k x => (B k x, fderiv ℝ (B k) x))
      (f₀ := fun x => (B₀ x, fderiv ℝ B₀ x))
      (g := potentialConnectionOperator (n := n))
      hpair hpair₀.continuousOn hU (contDiffOn_potentialConnectionOperator (n := n))
      hmap hpairconv
  · exact LocallyEventuallyBoundedDerivatives.comp_smooth
      (f := fun k x => (B k x, fderiv ℝ (B k) x))
      (f₀ := fun x => (B₀ x, fderiv ℝ B₀ x))
      (g := potentialConnectionOperator (n := n))
      hpairbound hpair hpair₀.continuousOn hU (contDiffOn_potentialConnectionOperator (n := n))
      hmap hpairconv

end PoincareConjecture
