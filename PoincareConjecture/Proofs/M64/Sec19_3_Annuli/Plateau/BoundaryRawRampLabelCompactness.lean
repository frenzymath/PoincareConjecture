import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryRealTraceCompactness
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryRampPhaseInverse












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Manifold

namespace PoincareConjecture.M64

open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.WeakCompactness

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)






theorem raw_ramp_label_weak_phase_subsequence
    (P : M62.CircleProductData F circumference) (gamma : ℝ → P.charts.Point)
    (L : M63PositiveDegreeLift P gamma)
    (sigma : ℕ → ℝ → ℝ) (hmono : ∀ j, Monotone (sigma j))
    (hperiod : ∀ j x, sigma j (x + curvePeriod) = sigma j x + curvePeriod)
    (hnormal : ∀ j, sigma j 0 ∈ Icc (0 : ℝ) curvePeriod)
    (u : ℕ → LoopPlane → ℝ) (V : ℕ → Fin 2 → LoopPlane → ℝ)
    (hu : ∀ j, MemLp (u j) 2 mu) (hV : ∀ j i, MemLp (V j i) 2 mu)
    (hw : ∀ j i, HasWeakPartialDeriv i (V j i) (u j) S)
    {C : ℝ} (hC : ∀ j i, (∫ p in S, (V j i p) ^ 2) ≤ C)
    (hseam : ∀ j, ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s ∈ Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
      (∫ p in S, phi p * V j 0 p) + (∫ p in S, fderiv ℝ phi p e0 * u j p) =
        ((L.degree : ℝ) * circumference) * ∫ s in Icc (0 : ℝ) 1,
          phi (annulusPoint curvePeriod s))
    (hgreen : ∀ j, ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ x : ℝ, phi (annulusPoint x 1) = 0) →
      (∫ p in S, phi p * V j 1 p) + (∫ p in S, fderiv ℝ phi p e1 * u j p) =
        -(∫ x in Icc (0 : ℝ) curvePeriod, phi (annulusPoint x 0) * L.lift (sigma j x))) :
    ∃ (k : ℕ → ℕ) (U : Lp ℝ 2 mu) (W : Fin 2 → Lp ℝ 2 mu) (tau : ℝ → ℝ),
      StrictMono k ∧ WeakConverges (fun j => (hu (k j)).toLp (u (k j))) U ∧
      (∀ i, WeakConverges (fun j => (hV (k j) i).toLp (V (k j) i)) (W i)) ∧
      (∀ᵐ p ∂mu, Tendsto (fun j => u (k j) p) atTop (𝓝 (U p))) ∧
      (∀ i, HasWeakPartialDeriv i (W i) U S) ∧
      Continuous tau ∧ Monotone tau ∧
      (∀ x, tau (x + curvePeriod) = tau x + curvePeriod) ∧
      tau 0 ∈ Icc (0 : ℝ) curvePeriod ∧
      (∀ x, Tendsto (fun j => sigma (k j) x) atTop (𝓝 (tau x))) ∧
      (∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
        (∀ s ∈ Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
        (∫ p in S, phi p * W 0 p) + (∫ p in S, fderiv ℝ phi p e0 * U p) =
          ((L.degree : ℝ) * circumference) * ∫ s in Icc (0 : ℝ) 1,
            phi (annulusPoint curvePeriod s)) ∧
      ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
        (∀ x : ℝ, phi (annulusPoint x 1) = 0) →
        (∫ p in S, phi p * W 1 p) + (∫ p in S, fderiv ℝ phi p e1 * U p) =
          -(∫ x in Icc (0 : ℝ) curvePeriod, phi (annulusPoint x 0) * L.lift (tau x)) := by
  let b := fun j x => L.lift (sigma j x)
  have hLmono : Monotone L.lift := (strictMono_of_deriv_pos L.derivative_positive).monotone
  have hbmono (j : ℕ) : Monotone (b j) := hLmono.comp (hmono j)
  have hbperiod (j : ℕ) (x : ℝ) :
      b j (x + curvePeriod) = b j x + (L.degree : ℝ) * circumference := by
    dsimp only [b]
    rw [hperiod, L.period_shift]
  let B := max |L.lift 0| |L.lift curvePeriod|
  have hbzero (j : ℕ) : |b j 0| ≤ B := by
    have hlo := hLmono (hnormal j).1
    have hhi := hLmono (hnormal j).2
    have hzero := abs_le.mp (le_max_left |L.lift 0| |L.lift curvePeriod|)
    have hP := abs_le.mp (le_max_right |L.lift 0| |L.lift curvePeriod|)
    rw [abs_le]
    change -B ≤ L.lift (sigma j 0) ∧ L.lift (sigma j 0) ≤ B
    dsimp only [B]
    constructor <;> linarith
  obtain ⟨k, U, W, c, hk, hU, hW, ha, hweak, hcmono, hc, hcperiod, -, hlim, hs, hg⟩ :=
    m64WeakPhase_monotone_real_trace_subsequence u V b hu hV hw hbmono hbperiod hbzero
      hC hseam hgreen
  obtain ⟨tau, htau, htaumono, htauperiod, hphase, hconvert⟩ :=
    positive_ramp_phase_recovers_label P gamma L c hc hcmono hcperiod
  have htend (x : ℝ) : Tendsto (fun j => sigma (k j) x) atTop (𝓝 (tau x)) :=
    hconvert (fun j => sigma (k j)) hlim x
  have hzero : tau 0 ∈ Icc (0 : ℝ) curvePeriod :=
    isClosed_Icc.mem_of_tendsto (htend 0) (Eventually.of_forall (fun j => hnormal (k j)))
  refine ⟨k, U, W, tau, hk, hU, hW, ha, hweak, htau, htaumono, htauperiod,
    hzero, htend, hs, ?_⟩
  intro phi hphi htop
  simpa only [hphase] using hg phi hphi htop

end PoincareConjecture.M64
