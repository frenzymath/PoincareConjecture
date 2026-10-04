import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Analysis.Covariant.Pairing
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Analysis.HarmonicCovariantTrace

/-!
# The plane-source Bochner identity in compatible coordinates

Morgan-Tian Claim 18.12, printed pp. 426-427, local curvature derivation.
The identity uses the actual coordinate derivatives and curvature of a
connection along a map. Harmonicity is an equation on the open domain;
no conclusion about stationarity is included in this calculation.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace PoincareMT.M60

open ConnectionVariation Poincare.Riemannian.RadialTransport

variable {P E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The coordinate coefficients of the pullback connection along a map.
Source: MT Section 3.2, covariant differentiation along maps. -/
def mapConnectionCoefficients (Γ : E → E →L[ℝ] E →L[ℝ] E) (u : P → E)
    (p : P) : P →L[ℝ] E →L[ℝ] E :=
  (Γ (u p)).comp (fderiv ℝ u p)

/-- The pullback connection is exactly covariant differentiation along
the map. Source: MT Section 3.2. -/
theorem covariantDerivative_mapConnectionCoefficients
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (u Y : P → E) (p d : P) :
    covariantDerivative (mapConnectionCoefficients Γ u) Y p d =
      covDerivAlong Γ u Y d p := rfl

/-- Smooth coordinate data give a smooth pullback connection.
Source: MT Section 3.2, coordinate connection formula. -/
theorem contDiffAt_mapConnectionCoefficients
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {u : P → E} {p : P}
    (hΓ : ContDiffAt ℝ ∞ Γ (u p)) (hu : ContDiffAt ℝ ∞ u p) :
    ContDiffAt ℝ ∞ (mapConnectionCoefficients Γ u) p :=
  (hΓ.comp p hu).clm_comp (hu.fderiv_right (by simp))

/-- The plane Bochner formula for the squared length of the first
coordinate derivative of a harmonic map. Source: MT Claim 18.12,
pp. 426-427, local Bochner derivation. -/
theorem harmonic_map_metric_bochner
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {u : P → E}
    {G : P → E →L[ℝ] E →L[ℝ] ℝ} {a : P → ℝ} {O : Set P} {p : P}
    (hO : IsOpen O) (hp : p ∈ O) (d e : P)
    (hu : ContDiffOn ℝ ∞ u O) (hG : ContDiffOn ℝ ∞ G O)
    (hΓ : ∀ q ∈ O, ContDiffAt ℝ ∞ Γ (u q))
    (hcompat : ∀ q ∈ O, ∀ v : P, ∀ b c : E,
      fderiv ℝ (fun r => G r b c) q v =
        G q (Γ (u q) (fderiv ℝ u q v) b) c +
          G q b (Γ (u q) (fderiv ℝ u q v) c))
    (hGsymm : ∀ b c : E, G p b c = G p c b)
    (hΓsymm : ∀ q ∈ O, ∀ b c, Γ (u q) b c = Γ (u q) c b)
    (hharm : ∀ q ∈ O,
      covDerivAlong Γ u (fun r => fderiv ℝ u r d) d q +
        covDerivAlong Γ u (fun r => fderiv ℝ u r e) e q = 0)
    (hnorm : ∀ q ∈ O, G q (fderiv ℝ u q d) (fderiv ℝ u q d) = a q) :
    fderiv ℝ (fun q => fderiv ℝ a q d) p d +
      fderiv ℝ (fun q => fderiv ℝ a q e) p e =
      2 * (G p (covDerivAlong Γ u (fun r => fderiv ℝ u r d) d p)
          (covDerivAlong Γ u (fun r => fderiv ℝ u r d) d p) +
        G p (covDerivAlong Γ u (fun r => fderiv ℝ u r d) e p)
          (covDerivAlong Γ u (fun r => fderiv ℝ u r d) e p)) +
      2 * G p (christoffelCurvature Γ (u p) (fderiv ℝ u p e)
        (fderiv ℝ u p d) (fderiv ℝ u p e)) (fderiv ℝ u p d) := by
  have hA : ContDiffOn ℝ ∞ (mapConnectionCoefficients Γ u) O := by
    intro q hq
    exact (contDiffAt_mapConnectionCoefficients (hΓ q hq)
      (hu.contDiffAt (hO.mem_nhds hq))).contDiffWithinAt
  have hY : ContDiffOn ℝ ∞ (fun q => fderiv ℝ u q d) O :=
    (hu.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
  have hnorm' : (fun q => G q (fderiv ℝ u q d) (fderiv ℝ u q d)) =ᶠ[𝓝 p] a :=
    Filter.Eventually.mono (hO.mem_nhds hp) fun q hq => hnorm q hq
  have hsecond (v : P) :
      fderiv ℝ (fun q => fderiv ℝ a q v) p v =
        2 * G p (covDerivAlong Γ u
          (covDerivAlong Γ u (fun r => fderiv ℝ u r d) v) v p) (fderiv ℝ u p d) +
        2 * G p (covDerivAlong Γ u (fun r => fderiv ℝ u r d) v p)
          (covDerivAlong Γ u (fun r => fderiv ℝ u r d) v p) := by
    have heq' : fderiv ℝ (fun q => G q (fderiv ℝ u q d) (fderiv ℝ u q d)) =ᶠ[𝓝 p]
        fderiv ℝ a := hnorm'.fderiv
    have heq : (fun q => fderiv ℝ (fun r => G r (fderiv ℝ u r d)
        (fderiv ℝ u r d)) q v) =ᶠ[𝓝 p] (fun q => fderiv ℝ a q v) :=
      heq'.mono fun q hq => congrArg (fun L => L v) hq
    rw [← heq.fderiv_eq]
    exact second_fderiv_metric_self hO hp hA hG hY hcompat hGsymm v
  have ht := covDerivAlong_harmonic_trace d e (hu.contDiffAt (hO.mem_nhds hp))
    (hΓ p hp) (Filter.Eventually.mono (hO.mem_nhds hp) fun q hq => hΓsymm q hq)
    (Filter.Eventually.mono (hO.mem_nhds hp) fun q hq => hharm q hq)
  have hpair := congrArg (fun v => G p v (fderiv ℝ u p d)) ht
  simp only [map_add, add_apply] at hpair
  rw [hsecond d, hsecond e]
  linarith

end PoincareMT.M60
