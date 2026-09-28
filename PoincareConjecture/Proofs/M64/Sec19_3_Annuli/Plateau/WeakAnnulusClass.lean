import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakDerivativeClosure
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ObservedTangentCoercivity

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff ENNReal

namespace PoincareConjecture

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

structure M64ObservedWeakAnnulus (e : M → E) (c0 c1 : ℝ → M) where
  map : LoopPlane → M
  observed_memLp : MemLp (e ∘ map) 2 mu
  column : Fin 2 → Lp E 2 mu
  tangent : ∀ i, ∀ᵐ p ∂mu, column i p ∈ range (mfderiv (𝓡 n) (𝓡 m) e (map p))
  weak_partial : ∀ i b, Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv i
    (fun p => column i p b) (fun p => e (map p) b) S
  boundary : ∀ (phi : LoopPlane → ℝ), ContDiff ℝ 1 phi →
    (∫ p in S, phi p • column 1 p) +
      (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single (1 : Fin 2) 1) • e (map p)) =
        ∫ x in Icc (0 : ℝ) curvePeriod,
          phi (annulusPoint x 1) • e (c1 x) - phi (annulusPoint x 0) • e (c0 x)
  seam : ∀ (phi : LoopPlane → ℝ), ContDiff ℝ 1 phi →
    (∀ s ∈ Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
    (∫ p in S, phi p • column 0 p) +
      (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single (0 : Fin 2) 1) • e (map p)) = 0

namespace M64ObservedWeakAnnulus

variable {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

def value (A : M64ObservedWeakAnnulus (n := n) e c0 c1) : Lp E 2 mu :=
  A.observed_memLp.toLp (e ∘ A.map)

def energy (B : M → E →L[ℝ] E →L[ℝ] ℝ)
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1) : ℝ :=
  ∫ p in S, (B (A.map p) (A.column 0 p) (A.column 0 p) +
    B (A.map p) (A.column 1 p) (A.column 1 p)) / 2

theorem energy_nonneg (B : M → E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ q v, 0 ≤ B q v v) (A : M64ObservedWeakAnnulus (n := n) e c0 c1) : 0 ≤ A.energy B :=
  integral_nonneg fun p => div_nonneg (add_nonneg (hB _ _) (hB _ _)) (by norm_num)

theorem map_aestronglyMeasurable (hei : IsEmbedding e)
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1) :
    AEStronglyMeasurable A.map mu := by
  let : TopologicalSpace.PseudoMetrizableSpace M := hei.isInducing.pseudoMetrizableSpace
  exact hei.aestronglyMeasurable_comp_iff.mp A.observed_memLp.aestronglyMeasurable

theorem column_energy_integrable (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    (hei : IsEmbedding e) {K : ℝ} (hb : ∀ q, ‖B q‖ ≤ K)
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1) (i : Fin 2) :
    IntegrableOn (fun p => B (A.map p) (A.column i p) (A.column i p)) S volume := by
  have hcoef := hB.comp_aestronglyMeasurable (A.map_aestronglyMeasurable hei)
  have hc : Continuous (fun q : (E →L[ℝ] E →L[ℝ] ℝ) × E => q.1 q.2 q.2) :=
    (continuous_fst.clm_apply continuous_snd).clm_apply continuous_snd
  have hm := hc.comp_aestronglyMeasurable (hcoef.prodMk (Lp.aestronglyMeasurable (A.column i)))
  have hi := (memLp_two_iff_integrable_sq_norm
    (Lp.aestronglyMeasurable (A.column i))).mp (Lp.memLp (A.column i))
  apply (hi.const_mul K).mono' hm
  filter_upwards with p
  have hop := (B (A.map p)).le_opNorm₂ (A.column i p) (A.column i p)
  have hmul := mul_le_mul_of_nonneg_right (hb (A.map p)) (sq_nonneg ‖A.column i p‖)
  nlinarith

theorem energy_integrable (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    (hei : IsEmbedding e) {K : ℝ} (hb : ∀ q, ‖B q‖ ≤ K)
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1) :
    IntegrableOn (fun p => (B (A.map p) (A.column 0 p) (A.column 0 p) +
      B (A.map p) (A.column 1 p) (A.column 1 p)) / 2) S volume :=
  ((A.column_energy_integrable B hB hei hb 0).add
    (A.column_energy_integrable B hB hei hb 1)).div_const 2

theorem column_norm_sq_le_energy
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    (hei : IsEmbedding e) {K : ℝ} (hb : ∀ q, ‖B q‖ ≤ K)
    (hpos : ∀ q v, 0 ≤ B q v v) {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * B q v v) (A : M64ObservedWeakAnnulus (n := n) e c0 c1) (i : Fin 2) :
    ‖A.column i‖ ^ 2 ≤ 2 * C * A.energy B := by
  rw [LpFiniteCoordinatesNative.l2_norm_sq]
  have hi := (memLp_two_iff_integrable_sq_norm
    (Lp.aestronglyMeasurable (A.column i))).mp (Lp.memLp (A.column i))
  calc
    _ ≤ ∫ p in S, 2 * C * ((B (A.map p) (A.column 0 p) (A.column 0 p) +
        B (A.map p) (A.column 1 p) (A.column 1 p)) / 2) := by
      apply integral_mono_ae hi ((A.energy_integrable B hB hei hb).const_mul _)
      filter_upwards [A.tangent i] with p hp
      have hc := hcoercive (A.map p) (A.column i p) hp
      have h0 := mul_nonneg hC (hpos (A.map p) (A.column 0 p))
      have h1 := mul_nonneg hC (hpos (A.map p) (A.column 1 p))
      fin_cases i
      · change ‖A.column 0 p‖ ^ 2 ≤ _
        change ‖A.column 0 p‖ ^ 2 ≤ C * B (A.map p) (A.column 0 p) (A.column 0 p) at hc
        linarith
      · change ‖A.column 1 p‖ ^ 2 ≤ _
        change ‖A.column 1 p‖ ^ 2 ≤ C * B (A.map p) (A.column 1 p) (A.column 1 p) at hc
        linarith
    _ = _ := integral_const_mul _ _

end M64ObservedWeakAnnulus

end PoincareConjecture
