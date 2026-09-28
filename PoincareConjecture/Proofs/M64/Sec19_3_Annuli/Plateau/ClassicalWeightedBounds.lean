import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeModulusReduction
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakPhaseDegreeEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeightedAnnulusEnergyIdentity

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain

namespace M64ObservedWeakAnnulus

omit [IsManifold (𝓡 n) ∞ M] in

theorem weightedEnergy_ge_vertical_boundary_mul_inv
    {e : M → E} {c0 c1 : ℝ → M}
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    (hei : IsEmbedding e) {K : ℝ} (hK : ∀ q, ‖Q q‖ ≤ K)
    (hpos : ∀ q v, 0 ≤ Q q v v) {C : ℝ}
    (hcoercive : ∀ (q : M) (v : E),
      v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
        ‖v‖ ^ 2 ≤ C * Q q v v)
    (hd : ContDiff ℝ 1 (fun x => e (c1 x) - e (c0 x)))
    {r : ℝ} (hr : 0 < r) :
    ((∫ x in Icc (0 : ℝ) curvePeriod,
      ‖e (c1 x) - e (c0 x)‖ ^ 2) / (2 * max C 1)) * r⁻¹ ≤
      A.weightedEnergy Q r := by
  have h := A.weightedEnergy_ge_vertical_boundary Q hQ hei hK hpos hcoercive hd hr
  convert h using 1; ring

omit [IsManifold (𝓡 n) ∞ M] in

theorem weightedEnergy_ge_phase_lift_mul
    {e : M → E} {c0 c1 : ℝ → M}
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    (hei : IsEmbedding e) {K : ℝ} (hK : ∀ q, ‖Q q‖ ≤ K)
    (hpos : ∀ q v, 0 ≤ Q q v v) {C : ℝ}
    (L : LoopPlane → ℝ) (hL : ContDiff ℝ 1 L) {d : ℝ}
    (hshift : ∀ x s, L (annulusPoint (x + curvePeriod) s) =
      L (annulusPoint x s) + d)
    (hder : ∀ᵐ p ∂volume.restrict S,
      (fderiv ℝ L p (EuclideanSpace.single (0 : Fin 2) 1)) ^ 2 ≤
        C * Q (A.map p) (A.column 0 p) (A.column 0 p))
    {r : ℝ} (hr : 0 < r) :
    (d ^ 2 / (2 * curvePeriod * max C 1)) * r ≤
      A.weightedEnergy Q r := by
  have h := A.weightedEnergy_ge_phase_lift Q hQ hei hK hpos L hL hshift hder hr
  convert h using 1; ring

end M64ObservedWeakAnnulus

theorem m64ClassicalWeightedGramEnergy_lower_of_observed
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M}
    (A : M64Annulus g c0 c1) (e : M → E)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      B q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) =
        g.inner q v v)
    (W : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (hmap : W.map = A.map)
    (hcols : ∀ i, ∀ᵐ p ∂volume.restrict S,
      W.column i p = fderiv ℝ (e ∘ A.map) p (EuclideanSpace.single i 1))
    {alpha beta r : ℝ}
    (halpha : alpha * r ≤ W.weightedEnergy B r)
    (hbeta : beta * r⁻¹ ≤ W.weightedEnergy B r) :
    alpha * r ≤ m64ClassicalWeightedGramEnergy g A r ∧
      beta * r⁻¹ ≤ m64ClassicalWeightedGramEnergy g A r := by
  have henergy := m64ObservedWeakAnnulus_seed_weightedEnergy_eq
    A e he B hdiag W hmap hcols r
  have henergy' : W.weightedEnergy B r =
      m64ClassicalWeightedGramEnergy g A r := by
    simpa only [m64ClassicalWeightedGramEnergy] using henergy
  rw [henergy'] at halpha hbeta
  exact ⟨halpha, hbeta⟩

end PoincareConjecture
