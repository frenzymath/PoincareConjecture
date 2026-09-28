import PoincareConjecture.Proofs.M03.Existence.MetricFamilyProducerNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckInverseCompositionNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckQuasilinearEstimateNative
import PoincareConjecture.Proofs.M03.Existence.ContinuousPathCompositionNative
import PoincareConjecture.Proofs.M03.Existence.SpectralShiftedNative
import PoincareConjecture.Proofs.M03.Existence.TimeL2BilinearNative
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped Manifold ContDiff Bundle BigOperators

noncomputable section

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [CompactSpace M]

structure NativeDeTurckFamily (g₀ : RiemannianMetric n M) where
  T : ℝ
  hT : 0 < T
  metric : ℝ → RiemannianMetric n M
  initial : metric 0 = g₀
  smooth : RiemannianMetric.IsSmoothFamilyOn metric (Set.Ico 0 T)
  equation : ∀ (t : ℝ), t ∈ Set.Ico 0 T → ∀ (x : M)
    (u v : TangentSpace (𝓡 n) x),
    HasDerivWithinAt (fun s => (metric s).inner x u v)
      (MetricFamilyProducerNative.deTurckRHS g₀ (metric t) x u v)
      (Set.Ico 0 T) t

namespace DeTurckMetricProducerNative

open MeasureTheory TensorProbeNative DeTurckInverseCompositionNative
open DeTurckNative DeTurckQuasilinearEstimateNative

def lowerPerturbationSource (background : MetricJet2 (n := n))
    (p : MetricLowerJet n) : Matrix (Fin n) (Fin n) ℝ :=
  lowerJetContraction p.1⁻¹ background.second + lowerJetSource background p

theorem perturbationRemainder_split (background : MetricJet2 (n := n))
    (dp : MetricLowerJet n) (DQ : MetricSecondJet n)
    (hp : (background.value + dp.1).PosDef)
    (hQm : ∀ a b i j, (background.second + DQ) a b i j =
      (background.second + DQ) a b j i)
    (hQd : ∀ a b i j, (background.second + DQ) a b i j =
      (background.second + DQ) b a i j) :
    perturbationRemainder background dp DQ =
      lowerJetContraction ((background.value + dp.1)⁻¹ - background.value⁻¹) DQ +
        lowerPerturbationSource background (backgroundLowerJet background + dp) := by
  rw [perturbationRemainder_eq, fixedPrincipalRemainder_split _ _ _ hp hQm hQd]
  simp only [lowerPerturbationSource, lowerJetContraction_add_right,
    lowerJetContraction_sub_left, backgroundLowerJet, Prod.fst_add]
  abel

variable [MeasurableSpace M] [BorelSpace M] (μ : Measure M) [IsFiniteMeasure μ]

def inverseCoefficientBound (n r : ℕ) (A I H : ℝ) : ℝ :=
  let J := inverseSupBound n (r + 1) A I
  let C := inverseL2Bound n (2 * r) A J
  let V := lpNorm (fun _ : M => (1 : ℝ)) 2 μ
  (n : ℝ) ^ 2 * (2 : ℝ) ^ (2 * r) * J ^ 2 +
    (n : ℝ) ^ 2 * (2 : ℝ) ^ (4 * r) * (J ^ 2 + 2 * J * C * (V + H))

theorem inverseCoefficientBound_nonneg (n r : ℕ) {A I H : ℝ}
    (hA : 0 ≤ A) (hI : 0 ≤ I) (hH : 0 ≤ H) :
    0 ≤ inverseCoefficientBound μ n r A I H := by
  have hJ := inverseSupBound_nonneg n (r + 1) hA hI
  have hC := inverseL2Bound_nonneg n (2 * r) hA hJ
  have hV : 0 ≤ lpNorm (fun _ : M => (1 : ℝ)) 2 μ := lpNorm_nonneg
  dsimp only [inverseCoefficientBound]
  positivity

theorem inverse_difference_bounds
    {iota : Type*} [Fintype iota]
    (F : iota → SmoothField (n := n) (M := M)) (r : ℕ)
    (G H : M → Matrix (Fin n) (Fin n) ℝ)
    (hG : ContMDiff (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) ∞ (fun x i j => G x i j))
    (hH : ContMDiff (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) ∞ (fun x i j => H x i j))
    (hGdet : ∀ x, (G x).det ≠ 0) (hHdet : ∀ x, (H x).det ≠ 0)
    {A I B δ : ℝ} (hA : 0 ≤ A) (hI : 0 ≤ I) (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hGLow : ∀ w : List iota, w.length ≤ r + 1 → ∀ (i j : Fin n) (x : M),
      ‖directionalWord F w (fun y => G y i j) x‖ ≤ A)
    (hHLow : ∀ w : List iota, w.length ≤ r + 1 → ∀ (i j : Fin n) (x : M),
      ‖directionalWord F w (fun y => H y i j) x‖ ≤ A)
    (hGInv : ∀ (i j : Fin n) (x : M), ‖(G x)⁻¹ i j‖ ≤ I)
    (hHInv : ∀ (i j : Fin n) (x : M), ‖(H x)⁻¹ i j‖ ≤ I)
    (hGHigh : ∀ w : List iota, w.length ≤ 2 * r → ∀ i j : Fin n,
      lpNorm (directionalWord F w (fun y => G y i j)) 2 μ ≤ B)
    (hHHigh : ∀ w : List iota, w.length ≤ 2 * r → ∀ i j : Fin n,
      lpNorm (directionalWord F w (fun y => H y i j)) 2 μ ≤ B)
    (hDLow : ∀ w : List iota, w.length ≤ r → ∀ (i j : Fin n) (x : M),
      ‖directionalWord F w (fun y => H y i j - G y i j) x‖ ≤ δ)
    (hDHigh : ∀ w : List iota, w.length ≤ 2 * r → ∀ i j : Fin n,
      lpNorm (directionalWord F w (fun y => H y i j - G y i j)) 2 μ ≤ δ) :
    (∀ w : List iota, w.length ≤ r → ∀ (i j : Fin n) (x : M),
      ‖directionalWord F w (fun y => (G y)⁻¹ i j - (H y)⁻¹ i j) x‖ ≤
        inverseCoefficientBound μ n r A I B * δ) ∧
    (∀ w : List iota, w.length ≤ 2 * r → ∀ i j : Fin n,
      lpNorm (directionalWord F w (fun y => (G y)⁻¹ i j - (H y)⁻¹ i j)) 2 μ ≤
        inverseCoefficientBound μ n r A I B * δ) := by
  let J := inverseSupBound n (r + 1) A I
  let C := inverseL2Bound n (2 * r) A J
  let V := lpNorm (fun _ : M => (1 : ℝ)) 2 μ
  let L := (n : ℝ) ^ 2 * (2 : ℝ) ^ (2 * r) * J ^ 2
  let K := (n : ℝ) ^ 2 * (2 : ℝ) ^ (4 * r) * (J ^ 2 + 2 * J * C * (V + B))
  have hJ : 0 ≤ J := inverseSupBound_nonneg n (r + 1) hA hI
  have hC : 0 ≤ C := inverseL2Bound_nonneg n (2 * r) hA hJ
  have hV : 0 ≤ V := lpNorm_nonneg
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hIG := norm_directionalWord_inverse_le F (r + 1) G hG hGdet hA hI hGLow hGInv
  have hIH := norm_directionalWord_inverse_le F (r + 1) H hH hHdet hA hI hHLow hHInv
  constructor
  · intro w hw i j x
    have h := norm_directionalWord_inverse_sub_le F r G H hG hH hGdet hHdet hJ hδ
      (fun w hw i j x => hIG w (by omega) i j x)
      (fun w hw i j x => hIH w (by omega) i j x) hDLow w hw i j x
    change _ ≤ (L + K) * δ
    exact h.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hK) hδ)
  · intro w hw i j
    have h := lpNorm_directionalWord_inverse_sub_le μ F (2 * r) G H hG hH hGdet hHdet
      hA hI hB hB hδ hδ
      (fun w hw => hGLow w (by omega)) (fun w hw => hHLow w (by omega))
      hGInv hHInv hGHigh hHHigh (fun w hw => hDLow w (by omega)) hDHigh w hw i j
    simp only [show 2 * r / 2 = r by omega] at h
    have hbound : lpNorm (directionalWord F w
        (fun y => (G y)⁻¹ i j - (H y)⁻¹ i j)) 2 μ ≤ K * δ := by
      convert h using 1 <;> dsimp [K, C, J, V] <;> ring
    change _ ≤ (L + K) * δ
    exact hbound.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hL) hδ)

structure MetricDerivativeBounds {iota : Type*} [Fintype iota]
    (F : iota → SmoothField (n := n) (M := M)) (r : ℕ) (A I B : ℝ)
    (G : M → Matrix (Fin n) (Fin n) ℝ) : Prop where
  smooth : ContMDiff (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) ∞ (fun x i j => G x i j)
  invertible : ∀ x, (G x).det ≠ 0
  low : ∀ w : List iota, w.length ≤ r + 1 → ∀ (i j : Fin n) (x : M),
    ‖directionalWord F w (fun y => G y i j) x‖ ≤ A
  inverse : ∀ (i j : Fin n) (x : M), ‖(G x)⁻¹ i j‖ ≤ I
  high : ∀ w : List iota, w.length ≤ 2 * r → ∀ i j : Fin n,
    lpNorm (directionalWord F w (fun y => G y i j)) 2 μ ≤ B

theorem inverse_principal_sub_mixed_le
    {iota : Type*} [Fintype iota]
    (F : iota → SmoothField (n := n) (M := M)) (r : ℕ)
    (G H G0 : M → Matrix (Fin n) (Fin n) ℝ)
    {A I B C U tu tv td Hd Hv : ℝ}
    (hA : 0 ≤ A) (hI : 0 ≤ I) (hB : 0 ≤ B) (hC : 0 ≤ C) (hU : 0 ≤ U)
    (htu : 0 ≤ tu) (htv : 0 ≤ tv) (htd : 0 ≤ td) (hHd : 0 ≤ Hd) (hHv : 0 ≤ Hv)
    (hG : MetricDerivativeBounds μ F r A I B G)
    (hH : MetricDerivativeBounds μ F r A I B H)
    (hG0 : MetricDerivativeBounds μ F r A I B G0)
    (hcenterLow : ∀ w : List iota, w.length ≤ r → ∀ (a b : Fin n) (x : M),
      ‖directionalWord F w (fun y => G0 y a b - G y a b) x‖ ≤ C * tu)
    (hcenterHigh : ∀ w : List iota, w.length ≤ 2 * r → ∀ a b : Fin n,
      lpNorm (directionalWord F w (fun y => G0 y a b - G y a b)) 2 μ ≤ C * tu)
    (hdiffLow : ∀ w : List iota, w.length ≤ r → ∀ (a b : Fin n) (x : M),
      ‖directionalWord F w (fun y => H y a b - G y a b) x‖ ≤ C * td)
    (hdiffHigh : ∀ w : List iota, w.length ≤ 2 * r → ∀ a b : Fin n,
      lpNorm (directionalWord F w (fun y => H y a b - G y a b)) 2 μ ≤ C * td)
    {u v : M → ℝ}
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ v)
    (huvLow : ∀ w : List iota, w.length ≤ r + 1 → ∀ x,
      ‖directionalWord F w (fun y => u y - v y) x‖ ≤ U * td)
    (hvLow : ∀ w : List iota, w.length ≤ r + 1 → ∀ x,
      ‖directionalWord F w v x‖ ≤ U * tv)
    (huvHigh : ∀ w : List iota, w.length ≤ 2 * r + 2 →
      lpNorm (directionalWord F w (fun y => u y - v y)) 2 μ ≤ U * Hd)
    (hvHigh : ∀ w : List iota, w.length ≤ 2 * r + 2 →
      lpNorm (directionalWord F w v) 2 μ ≤ U * Hv)
    (htraceDiff : td ≤ Hd) (htraceRight : tv ≤ Hv)
    (w : List iota) (hw : w.length ≤ 2 * r) (i j : iota) (a b : Fin n) :
    lpNorm (directionalWord F w (fun x =>
      ((G x)⁻¹ a b - (G0 x)⁻¹ a b) * directionalWord F [i, j] u x -
        ((H x)⁻¹ a b - (G0 x)⁻¹ a b) * directionalWord F [i, j] v x)) 2 μ ≤
      (2 : ℝ) ^ (w.length + 1) * inverseCoefficientBound μ n r A I B * C * U *
        (max tu tv * Hd + td * Hv) := by
  let L := inverseCoefficientBound μ n r A I B
  have hL : 0 ≤ L := inverseCoefficientBound_nonneg μ n r hA hI hB
  have hcenter := inverse_difference_bounds μ F r G G0 hG.smooth hG0.smooth
    hG.invertible hG0.invertible hA hI hB (mul_nonneg hC htu)
    hG.low hG0.low hG.inverse hG0.inverse hG.high hG0.high hcenterLow hcenterHigh
  have hdiff := inverse_difference_bounds μ F r G H hG.smooth hH.smooth
    hG.invertible hH.invertible hA hI hB (mul_nonneg hC htd)
    hG.low hH.low hG.inverse hH.inverse hG.high hH.high hdiffLow hdiffHigh
  let f : M → ℝ := fun x => (G x)⁻¹ a b - (G0 x)⁻¹ a b
  let g : M → ℝ := fun x => (H x)⁻¹ a b - (G0 x)⁻¹ a b
  have hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f :=
    (inverse_entry_contMDiff G hG.smooth hG.invertible a b).sub
      (inverse_entry_contMDiff G0 hG0.smooth hG0.invertible a b)
  have hg : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ g :=
    (inverse_entry_contMDiff H hH.smooth hH.invertible a b).sub
      (inverse_entry_contMDiff G0 hG0.smooth hG0.invertible a b)
  have hfg : (fun x => f x - g x) = fun x => (G x)⁻¹ a b - (H x)⁻¹ a b := by
    funext x
    dsimp only [f, g]
    ring
  have hfLow : ∀ z : List iota, z.length ≤ r → ∀ x,
      ‖directionalWord F z f x‖ ≤ (L * C) * tu := by
    intro z hz x
    simpa only [mul_assoc] using hcenter.1 z hz a b x
  have hfHigh : ∀ z : List iota, z.length ≤ 2 * r →
      lpNorm (directionalWord F z f) 2 μ ≤ (L * C) * tu := by
    intro z hz
    simpa only [mul_assoc] using hcenter.2 z hz a b
  have hfgLow : ∀ z : List iota, z.length ≤ r → ∀ x,
      ‖directionalWord F z (fun x => f x - g x) x‖ ≤ (L * C) * td := by
    intro z hz x
    rw [hfg]
    simpa only [mul_assoc] using hdiff.1 z hz a b x
  have hfgHigh : ∀ z : List iota, z.length ≤ 2 * r →
      lpNorm (directionalWord F z (fun x => f x - g x)) 2 μ ≤ (L * C) * td := by
    intro z hz
    rw [hfg]
    simpa only [mul_assoc] using hdiff.2 z hz a b
  have h := DeTurckQuasilinearEstimateNative.lpNorm_directionalWord_principal_sub_mixed_le
    μ F r w hw i j hf hg hu hv (mul_nonneg hL hC) hU htu htv htd hHd hHv
    htraceDiff htraceRight hfLow huvLow hfgLow hvLow hfHigh huvHigh hfgHigh hvHigh
  simpa only [L, f, g, mul_assoc] using h

def lowerPerturbationBudget (q r : ℕ) (v p a : ℝ × ℝ) (c c1 c2 : ℝ) : ℝ × ℝ :=
  budgetSum q (budgetSum q (budgetProduct r a (c2, 0))) +
    lowerJetSourceBudget q r v p a c c1

theorem lowerPerturbationSource_difference_bounds
    {iota : Type*} [Fintype iota]
    (F : iota → SmoothField (n := n) (M := M)) (r : ℕ) (δ : ℝ)
    (v p a : ℝ × ℝ) (c c1 c2 : ℝ)
    (background : M → MetricJet2 (n := n)) (G H : M → MetricLowerJet n)
    (hvalue : ∀ i j : Fin n, ScalarDifferenceBounds μ F r δ v
      (fun x => (G x).1 i j) (fun x => (H x).1 i j))
    (hfirst : ∀ b i j : Fin n, ScalarDifferenceBounds μ F r δ p
      (fun x => (G x).2 b i j) (fun x => (H x).2 b i j))
    (hinverse : ∀ i j : Fin n, ScalarDifferenceBounds μ F r δ a
      (fun x => (G x).1⁻¹ i j) (fun x => (H x).1⁻¹ i j))
    (hbackground : ∀ k i j : Fin n, ScalarDerivativeBounds μ F r c
      (fun x => christoffelJet (background x) k i j))
    (hbackground1 : ∀ b k i j : Fin n, ScalarDerivativeBounds μ F r c1
      (fun x => christoffelSecond (background x) b k i j))
    (hbackground2 : ∀ a b i j : Fin n, ScalarDerivativeBounds μ F r c2
      (fun x => (background x).second a b i j)) :
    ∀ i j : Fin n,
      ScalarDifferenceBounds μ F r δ (lowerPerturbationBudget n r v p a c c1 c2)
        (fun x => lowerPerturbationSource (background x) (G x) i j)
        (fun x => lowerPerturbationSource (background x) (H x) i j) := by
  have hsource := lowerJetSource_directional_difference_bounds μ F r δ v p a c c1
    background G H hvalue hfirst hinverse hbackground hbackground1
  intro i j
  exact (ScalarDifferenceBounds.finSum _ _ (fun k =>
    ScalarDifferenceBounds.finSum _ _ (fun l =>
      (hinverse k l).mul (ScalarDifferenceBounds.refl (hbackground2 k l i j))))).add
        (hsource i j)

theorem perturbationRemainder_directional_difference_le
    {iota : Type*} [Fintype iota]
    (F : iota → SmoothField (n := n) (M := M)) (r : ℕ)
    (background : M → MetricJet2 (n := n))
    (dp dq : M → MetricLowerJet n) (DQ DS : M → MetricSecondJet n)
    (hG : ∀ x, ((background x).value + (dp x).1).PosDef)
    (hH : ∀ x, ((background x).value + (dq x).1).PosDef)
    (hQm : ∀ x a b i j, ((background x).second + DQ x) a b i j =
      ((background x).second + DQ x) a b j i)
    (hQd : ∀ x a b i j, ((background x).second + DQ x) a b i j =
      ((background x).second + DQ x) b a i j)
    (hSm : ∀ x a b i j, ((background x).second + DS x) a b i j =
      ((background x).second + DS x) a b j i)
    (hSd : ∀ x a b i j, ((background x).second + DS x) a b i j =
      ((background x).second + DS x) b a i j)
    {P L δ : ℝ}
    (hprincipalSmooth : ∀ a b i j : Fin n, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun x => (((background x).value + (dp x).1)⁻¹ a b -
          ((background x).value)⁻¹ a b) * DQ x a b i j -
        (((background x).value + (dq x).1)⁻¹ a b -
          ((background x).value)⁻¹ a b) * DS x a b i j))
    (hlower : ∀ i j : Fin n, ScalarDerivativeBounds μ F r (L * δ)
      (fun x =>
        lowerPerturbationSource (background x) (backgroundLowerJet (background x) + dp x) i j -
          lowerPerturbationSource (background x)
            (backgroundLowerJet (background x) + dq x) i j))
    (w : List iota) (hw : w.length ≤ 2 * r)
    (hprincipal : ∀ a b i j : Fin n,
      lpNorm (directionalWord F w (fun x =>
        (((background x).value + (dp x).1)⁻¹ a b -
          ((background x).value)⁻¹ a b) * DQ x a b i j -
        (((background x).value + (dq x).1)⁻¹ a b -
          ((background x).value)⁻¹ a b) * DS x a b i j)) 2 μ ≤ P)
    (i j : Fin n) :
    lpNorm (directionalWord F w (fun x =>
      perturbationRemainder (background x) (dp x) (DQ x) i j -
        perturbationRemainder (background x) (dq x) (DS x) i j)) 2 μ ≤
      (n : ℝ) ^ 2 * P + L * δ := by
  classical
  let f : Fin n → Fin n → M → ℝ := fun a b x =>
    (((background x).value + (dp x).1)⁻¹ a b -
      ((background x).value)⁻¹ a b) * DQ x a b i j -
    (((background x).value + (dq x).1)⁻¹ a b -
      ((background x).value)⁻¹ a b) * DS x a b i j
  let l : M → ℝ := fun x =>
    lowerPerturbationSource (background x) (backgroundLowerJet (background x) + dp x) i j -
      lowerPerturbationSource (background x) (backgroundLowerJet (background x) + dq x) i j
  have hf (a b : Fin n) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f a b) :=
    hprincipalSmooth a b i j
  have hs (a : Fin n) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => ∑ b, f a b x) :=
    ContMDiff.sum (t := Finset.univ) (fun b _ => hf a b)
  have hsum : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => ∑ a, ∑ b, f a b x) :=
    ContMDiff.sum (t := Finset.univ) (fun a _ => hs a)
  have hLpSum (q : Fin n → M → ℝ)
      (hq : ∀ a, Continuous (q a)) :
      lpNorm (fun x => ∑ a, q a x) 2 μ ≤ ∑ a, lpNorm (q a) 2 μ := by
    rw [show (fun x => ∑ a, q a x) = ∑ a, q a from by
      funext x; simp only [Finset.sum_apply]]
    exact lpNorm_sum_le (s := Finset.univ) (f := q)
        (fun a _ => ContinuousMap.memLp (p := 2) (μ := μ) ℝ
          (⟨q a, hq a⟩ : C(M, ℝ))) (by norm_num : (1 : ENNReal) ≤ 2)
  have heq : (fun x => perturbationRemainder (background x) (dp x) (DQ x) i j -
      perturbationRemainder (background x) (dq x) (DS x) i j) =
      fun x => (∑ a, ∑ b, f a b x) + l x := by
    funext x
    rw [perturbationRemainder_split _ _ _ (hG x) (hQm x) (hQd x),
      perturbationRemainder_split _ _ _ (hH x) (hSm x) (hSd x)]
    simp only [lowerJetContraction, Matrix.add_apply, Matrix.sub_apply, f, l,
      Finset.sum_sub_distrib]
    ring
  have hsumD : directionalWord F w (fun x => ∑ a, ∑ b, f a b x) =
      fun x => ∑ a, ∑ b, directionalWord F w (f a b) x := by
    funext x
    rw [directionalWord_sum Finset.univ F w _ (fun a _ => hs a)]
    apply Finset.sum_congr rfl
    intro a _
    exact directionalWord_sum Finset.univ F w _ (fun b _ => hf a b) x
  have hbound : lpNorm (directionalWord F w (fun x => ∑ a, ∑ b, f a b x)) 2 μ ≤
      (n : ℝ) ^ 2 * P := by
    rw [hsumD]
    calc
      _ ≤ ∑ a : Fin n, ∑ b : Fin n, lpNorm (directionalWord F w (f a b)) 2 μ := by
        apply (hLpSum _
          (fun a => (ContMDiff.sum (t := Finset.univ)
            (fun b _ => directionalWord_contMDiff F w (hf a b))).continuous)).trans
        exact Finset.sum_le_sum (fun a _ =>
          hLpSum _
            (fun b => (directionalWord_contMDiff F w (hf a b)).continuous))
      _ ≤ ∑ _a : Fin n, ∑ _b : Fin n, P :=
        Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hprincipal a b i j))
      _ = _ := by simp [pow_two, mul_assoc]
  have hadd (z : List iota) :
      directionalWord F z (fun x => (∑ a, ∑ b, f a b x) + l x) =
        fun x => directionalWord F z (fun y => ∑ a, ∑ b, f a b y) x +
          directionalWord F z l x := by
    induction z with
    | nil => rfl
    | cons k z ih =>
      funext x
      rw [directionalWord_cons, ih]
      exact congrArg (fun L : TangentSpace (𝓡 n) x →L[ℝ] ℝ => L (F k x))
        (mfderiv_add ((directionalWord_contMDiff F z hsum).mdifferentiable (by simp) x)
          ((directionalWord_contMDiff F z (hlower i j).smooth).mdifferentiable (by simp) x))
  rw [heq, hadd]
  exact (lpNorm_add_le
    (ContinuousMap.memLp (p := 2) (μ := μ) ℝ
      (⟨_, (directionalWord_contMDiff F w hsum).continuous⟩ : C(M, ℝ)))
    (by norm_num : (1 : ENNReal) ≤ 2)).trans
      (add_le_add hbound ((hlower i j).high w hw))

section JointSourceRegularity

open scoped Matrix.Norms.Elementwise

theorem contDiffAt_jointChartStateSource_infty
    (z : ChartState (n := n) × ChartState (n := n))
    (hB : z.1.1.PosDef) (hg : z.2.1.PosDef) :
    ContDiffAt ℝ ∞
      (fun q : ChartState (n := n) × ChartState (n := n) =>
        chartStateSource (chartStateJet q.1) q.2) z := by
  let J : Bool → ChartState (n := n) × ChartState (n := n) → MetricJet2 (n := n) :=
    fun b q => chartStateJet (if b then q.1 else q.2)
  have hvalue (b : Bool) : ContDiffAt ℝ ∞
      (fun q => fun i j => (J b q).value i j) z := by
    cases b
    · change ContDiffAt ℝ ∞
        (fun q : ChartState (n := n) × ChartState (n := n) => fun i j => q.2.1 i j) z
      fun_prop
    · change ContDiffAt ℝ ∞
        (fun q : ChartState (n := n) × ChartState (n := n) => fun i j => q.1.1 i j) z
      fun_prop
  have hfirst (b : Bool) (a i j : Fin n) : ContDiffAt ℝ ∞
      (fun q => (J b q).first a i j) z := by
    cases b
    · change ContDiffAt ℝ ∞
        (fun q : ChartState (n := n) × ChartState (n := n) => q.2.2.1 a i j) z
      fun_prop
    · change ContDiffAt ℝ ∞
        (fun q : ChartState (n := n) × ChartState (n := n) => q.1.2.1 a i j) z
      fun_prop
  have hsecond (b : Bool) (a c i j : Fin n) : ContDiffAt ℝ ∞
      (fun q => (J b q).second a c i j) z := by
    cases b
    · change ContDiffAt ℝ ∞
        (fun q : ChartState (n := n) × ChartState (n := n) => q.2.2.2 a c i j) z
      fun_prop
    · change ContDiffAt ℝ ∞
        (fun q : ChartState (n := n) × ChartState (n := n) => q.1.2.2 a c i j) z
      fun_prop
  have hpos (b : Bool) : (J b z).value.PosDef := by
    cases b
    · exact hg
    · exact hB
  have hinverse (b : Bool) : ContDiffAt ℝ ∞
      (fun q => matrixInverseEntries (fun i j => (J b q).value i j)) z :=
    (contDiffAt_matrixInverseEntries_infty _
      (((J b z).value.isUnit_iff_isUnit_det.mp (hpos b).isUnit).ne_zero)).comp
        (f := fun q => fun i j => (J b q).value i j) (g := matrixInverseEntries)
        z (hvalue b)
  have hv (b : Bool) (i j : Fin n) : ContDiffAt ℝ ∞
      (fun q => (J b q).value i j) z :=
    contDiffAt_pi.mp (contDiffAt_pi.mp (hvalue b) i) j
  have hi (b : Bool) (i j : Fin n) : ContDiffAt ℝ ∞
      (fun q => (J b q).value⁻¹ i j) z :=
    contDiffAt_pi.mp (contDiffAt_pi.mp (hinverse b) i) j
  have hconnection (b : Bool) (k i j : Fin n) : ContDiffAt ℝ ∞
      (fun q => christoffelJet (J b q) k i j) z := by
    unfold christoffelJet
    apply contDiffAt_const.mul
    exact ContDiffAt.sum (fun l _ => (hi b k l).mul
      (((hfirst b i l j).add (hfirst b j l i)).sub (hfirst b l i j)))
  have hinverseFirst (b : Bool) (a k l : Fin n) : ContDiffAt ℝ ∞
      (fun q => inverseFirst (J b q) a k l) z := by
    unfold inverseFirst
    apply ContDiffAt.neg
    exact ContDiffAt.sum (fun u _ => ContDiffAt.sum (fun v _ =>
      ((hi b k u).mul (hfirst b a u v)).mul (hi b v l)))
  have hconnectionFirst (b : Bool) (a k i j : Fin n) : ContDiffAt ℝ ∞
      (fun q => christoffelSecond (J b q) a k i j) z := by
    unfold christoffelSecond
    apply contDiffAt_const.mul
    exact ContDiffAt.sum (fun l _ =>
      ((hinverseFirst b a k l).mul
        (((hfirst b i l j).add (hfirst b j l i)).sub (hfirst b l i j))).add
      ((hi b k l).mul
        (((hsecond b a i l j).add (hsecond b a j l i)).sub (hsecond b a l i j))))
  have hcurvature (i j k l : Fin n) : ContDiffAt ℝ ∞
      (fun q => mixedCurvatureJet (J false q) i j k l) z := by
    unfold mixedCurvatureJet
    exact ((hconnectionFirst false i l j k).sub (hconnectionFirst false j l i k)).add
      (ContDiffAt.sum (fun m _ =>
        ((hconnection false m j k).mul (hconnection false l i m)).sub
          ((hconnection false m i k).mul (hconnection false l j m))))
  have hricci (i j : Fin n) : ContDiffAt ℝ ∞
      (fun q => ricciJet (J false q) i j) z :=
    ContDiffAt.sum (fun k _ => hcurvature k i j k)
  have hfield (k : Fin n) : ContDiffAt ℝ ∞
      (fun q => deTurckVector (J true q) (J false q) k) z := by
    unfold deTurckVector
    exact ContDiffAt.sum (fun a _ => ContDiffAt.sum (fun b _ =>
      (hi false a b).mul ((hconnection false k a b).sub (hconnection true k a b))))
  have hfieldFirst (a k : Fin n) : ContDiffAt ℝ ∞
      (fun q => deTurckVectorFirst (J true q) (J false q) a k) z := by
    unfold deTurckVectorFirst
    exact ContDiffAt.sum (fun u _ => ContDiffAt.sum (fun v _ =>
      ((hinverseFirst false a u v).mul
        ((hconnection false k u v).sub (hconnection true k u v))).add
      ((hi false u v).mul
        ((hconnectionFirst false a k u v).sub (hconnectionFirst true a k u v)))))
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  change ContDiffAt ℝ ∞ (fun q => -2 * ricciJet (J false q) i j +
    ∑ k, (deTurckVector (J true q) (J false q) k * (J false q).first k i j +
      (J false q).value k j * deTurckVectorFirst (J true q) (J false q) i k +
        (J false q).value i k * deTurckVectorFirst (J true q) (J false q) j k)) z
  exact (contDiffAt_const.mul (hricci i j)).add (ContDiffAt.sum (fun k _ =>
    (((hfield k).mul (hfirst false k i j)).add ((hv false k j).mul (hfieldFirst i k))).add
      ((hv false i k).mul (hfieldFirst j k))))

theorem contDiffAt_jointLowerJetSource_infty
    (z : ChartState (n := n) × MetricLowerJet n)
    (hB : z.1.1.PosDef) (hp : z.2.1.PosDef) :
    ContDiffAt ℝ ∞
      (fun q : ChartState (n := n) × MetricLowerJet n =>
        lowerJetSource (chartStateJet q.1) q.2) z := by
  have hslots : ContDiffAt ℝ ∞
      (fun q : ChartState (n := n) × MetricLowerJet n =>
        (q.1, lowerJetState q.2 0)) z := by
    exact contDiffAt_fst.prodMk
      (contDiffAt_snd.fst.prodMk (contDiffAt_snd.snd.prodMk contDiffAt_const))
  exact (contDiffAt_jointChartStateSource_infty
    (z.1, lowerJetState z.2 0) hB hp).comp z hslots

theorem contDiffAt_jointLowerPerturbationSource_infty
    (z : ChartState (n := n) × MetricLowerJet n)
    (hB : z.1.1.PosDef) (hp : z.2.1.PosDef) :
    ContDiffAt ℝ ∞
      (fun q : ChartState (n := n) × MetricLowerJet n =>
        lowerPerturbationSource (chartStateJet q.1) q.2) z := by
  have hinverse : ContDiffAt ℝ ∞
      (fun q : ChartState (n := n) × MetricLowerJet n =>
        matrixInverseEntries (fun i j => q.2.1 i j)) z :=
    (contDiffAt_matrixInverseEntries_infty _
      ((z.2.1.isUnit_iff_isUnit_det.mp hp.isUnit).ne_zero)).comp
        (f := fun q : ChartState (n := n) × MetricLowerJet n => fun i j => q.2.1 i j)
        (g := matrixInverseEntries) z (by fun_prop)
  have hi (a b : Fin n) : ContDiffAt ℝ ∞
      (fun q : ChartState (n := n) × MetricLowerJet n => q.2.1⁻¹ a b) z :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hinverse a) b
  have hcontraction : ContDiffAt ℝ ∞
      (fun q : ChartState (n := n) × MetricLowerJet n =>
        lowerJetContraction q.2.1⁻¹ q.1.2.2) z := by
    apply contDiffAt_pi.mpr
    intro i
    apply contDiffAt_pi.mpr
    intro j
    exact ContDiffAt.sum (fun a _ => ContDiffAt.sum (fun b _ =>
      (hi a b).mul (by fun_prop)))
  exact hcontraction.add (contDiffAt_jointLowerJetSource_infty z hB hp)

end JointSourceRegularity

section CompactRangeRegularity

open Set Filter Metric
open scoped Topology Matrix.Norms.Elementwise

theorem contDiffAt_jointChartStateSource_of_det_ne_zero
    (z : ChartState (n := n) × ChartState (n := n))
    (hB : z.1.1.det ≠ 0) (hg : z.2.1.det ≠ 0) :
    ContDiffAt ℝ ∞
      (fun q : ChartState (n := n) × ChartState (n := n) =>
        chartStateSource (chartStateJet q.1) q.2) z := by
  let J : Bool → ChartState (n := n) × ChartState (n := n) → MetricJet2 (n := n) :=
    fun b q => chartStateJet (if b then q.1 else q.2)
  have hvalue (b : Bool) : ContDiffAt ℝ ∞
      (fun q => fun i j => (J b q).value i j) z := by
    cases b
    · change ContDiffAt ℝ ∞
        (fun q : ChartState (n := n) × ChartState (n := n) => fun i j => q.2.1 i j) z
      fun_prop
    · change ContDiffAt ℝ ∞
        (fun q : ChartState (n := n) × ChartState (n := n) => fun i j => q.1.1 i j) z
      fun_prop
  have hfirst (b : Bool) (a i j : Fin n) : ContDiffAt ℝ ∞
      (fun q => (J b q).first a i j) z := by
    cases b
    · change ContDiffAt ℝ ∞
        (fun q : ChartState (n := n) × ChartState (n := n) => q.2.2.1 a i j) z
      fun_prop
    · change ContDiffAt ℝ ∞
        (fun q : ChartState (n := n) × ChartState (n := n) => q.1.2.1 a i j) z
      fun_prop
  have hsecond (b : Bool) (a c i j : Fin n) : ContDiffAt ℝ ∞
      (fun q => (J b q).second a c i j) z := by
    cases b
    · change ContDiffAt ℝ ∞
        (fun q : ChartState (n := n) × ChartState (n := n) => q.2.2.2 a c i j) z
      fun_prop
    · change ContDiffAt ℝ ∞
        (fun q : ChartState (n := n) × ChartState (n := n) => q.1.2.2 a c i j) z
      fun_prop
  have hdet (b : Bool) : (J b z).value.det ≠ 0 := by
    cases b
    · exact hg
    · exact hB
  have hinverse (b : Bool) : ContDiffAt ℝ ∞
      (fun q => matrixInverseEntries (fun i j => (J b q).value i j)) z :=
    (contDiffAt_matrixInverseEntries_infty _ (hdet b)).comp
      (f := fun q => fun i j => (J b q).value i j) (g := matrixInverseEntries)
      z (hvalue b)
  have hv (b : Bool) (i j : Fin n) : ContDiffAt ℝ ∞
      (fun q => (J b q).value i j) z :=
    contDiffAt_pi.mp (contDiffAt_pi.mp (hvalue b) i) j
  have hi (b : Bool) (i j : Fin n) : ContDiffAt ℝ ∞
      (fun q => (J b q).value⁻¹ i j) z :=
    contDiffAt_pi.mp (contDiffAt_pi.mp (hinverse b) i) j
  have hconnection (b : Bool) (k i j : Fin n) : ContDiffAt ℝ ∞
      (fun q => christoffelJet (J b q) k i j) z := by
    unfold christoffelJet
    apply contDiffAt_const.mul
    exact ContDiffAt.sum (fun l _ => (hi b k l).mul
      (((hfirst b i l j).add (hfirst b j l i)).sub (hfirst b l i j)))
  have hinverseFirst (b : Bool) (a k l : Fin n) : ContDiffAt ℝ ∞
      (fun q => inverseFirst (J b q) a k l) z := by
    unfold inverseFirst
    apply ContDiffAt.neg
    exact ContDiffAt.sum (fun u _ => ContDiffAt.sum (fun v _ =>
      ((hi b k u).mul (hfirst b a u v)).mul (hi b v l)))
  have hconnectionFirst (b : Bool) (a k i j : Fin n) : ContDiffAt ℝ ∞
      (fun q => christoffelSecond (J b q) a k i j) z := by
    unfold christoffelSecond
    apply contDiffAt_const.mul
    exact ContDiffAt.sum (fun l _ =>
      ((hinverseFirst b a k l).mul
        (((hfirst b i l j).add (hfirst b j l i)).sub (hfirst b l i j))).add
      ((hi b k l).mul
        (((hsecond b a i l j).add (hsecond b a j l i)).sub (hsecond b a l i j))))
  have hcurvature (i j k l : Fin n) : ContDiffAt ℝ ∞
      (fun q => mixedCurvatureJet (J false q) i j k l) z := by
    unfold mixedCurvatureJet
    exact ((hconnectionFirst false i l j k).sub (hconnectionFirst false j l i k)).add
      (ContDiffAt.sum (fun m _ =>
        ((hconnection false m j k).mul (hconnection false l i m)).sub
          ((hconnection false m i k).mul (hconnection false l j m))))
  have hricci (i j : Fin n) : ContDiffAt ℝ ∞
      (fun q => ricciJet (J false q) i j) z :=
    ContDiffAt.sum (fun k _ => hcurvature k i j k)
  have hfield (k : Fin n) : ContDiffAt ℝ ∞
      (fun q => deTurckVector (J true q) (J false q) k) z := by
    unfold deTurckVector
    exact ContDiffAt.sum (fun a _ => ContDiffAt.sum (fun b _ =>
      (hi false a b).mul ((hconnection false k a b).sub (hconnection true k a b))))
  have hfieldFirst (a k : Fin n) : ContDiffAt ℝ ∞
      (fun q => deTurckVectorFirst (J true q) (J false q) a k) z := by
    unfold deTurckVectorFirst
    exact ContDiffAt.sum (fun u _ => ContDiffAt.sum (fun v _ =>
      ((hinverseFirst false a u v).mul
        ((hconnection false k u v).sub (hconnection true k u v))).add
      ((hi false u v).mul
        ((hconnectionFirst false a k u v).sub (hconnectionFirst true a k u v)))))
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  change ContDiffAt ℝ ∞ (fun q => -2 * ricciJet (J false q) i j +
    ∑ k, (deTurckVector (J true q) (J false q) k * (J false q).first k i j +
      (J false q).value k j * deTurckVectorFirst (J true q) (J false q) i k +
        (J false q).value i k * deTurckVectorFirst (J true q) (J false q) j k)) z
  exact (contDiffAt_const.mul (hricci i j)).add (ContDiffAt.sum (fun k _ =>
    (((hfield k).mul (hfirst false k i j)).add ((hv false k j).mul (hfieldFirst i k))).add
      ((hv false i k).mul (hfieldFirst j k))))

theorem contDiffAt_jointLowerJetSource_of_det_ne_zero
    (z : ChartState (n := n) × MetricLowerJet n)
    (hB : z.1.1.det ≠ 0) (hp : z.2.1.det ≠ 0) :
    ContDiffAt ℝ ∞
      (fun q : ChartState (n := n) × MetricLowerJet n =>
        lowerJetSource (chartStateJet q.1) q.2) z := by
  have hslots : ContDiffAt ℝ ∞
      (fun q : ChartState (n := n) × MetricLowerJet n =>
        (q.1, lowerJetState q.2 0)) z := by
    exact contDiffAt_fst.prodMk
      (contDiffAt_snd.fst.prodMk (contDiffAt_snd.snd.prodMk contDiffAt_const))
  exact (contDiffAt_jointChartStateSource_of_det_ne_zero
    (z.1, lowerJetState z.2 0) hB hp).comp z hslots

theorem contDiffAt_jointLowerPerturbationSource_of_det_ne_zero
    (z : ChartState (n := n) × MetricLowerJet n)
    (hB : z.1.1.det ≠ 0) (hp : z.2.1.det ≠ 0) :
    ContDiffAt ℝ ∞
      (fun q : ChartState (n := n) × MetricLowerJet n =>
        lowerPerturbationSource (chartStateJet q.1) q.2) z := by
  have hinverse : ContDiffAt ℝ ∞
      (fun q : ChartState (n := n) × MetricLowerJet n =>
        matrixInverseEntries (fun i j => q.2.1 i j)) z :=
    (contDiffAt_matrixInverseEntries_infty _ hp).comp
      (f := fun q : ChartState (n := n) × MetricLowerJet n => fun i j => q.2.1 i j)
      (g := matrixInverseEntries) z (by fun_prop)
  have hi (a b : Fin n) : ContDiffAt ℝ ∞
      (fun q : ChartState (n := n) × MetricLowerJet n => q.2.1⁻¹ a b) z :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hinverse a) b
  have hcontraction : ContDiffAt ℝ ∞
      (fun q : ChartState (n := n) × MetricLowerJet n =>
        lowerJetContraction q.2.1⁻¹ q.1.2.2) z := by
    apply contDiffAt_pi.mpr
    intro i
    apply contDiffAt_pi.mpr
    intro j
    exact ContDiffAt.sum (fun a _ => ContDiffAt.sum (fun b _ =>
      (hi a b).mul (by fun_prop)))
  exact hcontraction.add (contDiffAt_jointLowerJetSource_of_det_ne_zero z hB hp)

theorem exists_contDiff_extension_near_compact
    {V W : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {S U : Set V} (hS : IsCompact S) (hU : IsOpen U) (hSU : S ⊆ U)
    (f : V → W) (hf : ∀ x ∈ U, ContDiffAt ℝ ∞ f x) :
    ∃ fExt : C(V, W), ContDiff ℝ ∞ fExt ∧
      ∃ O : Set V, IsOpen O ∧ S ⊆ O ∧ EqOn fExt f O := by
  have hd : Disjoint Uᶜ S := disjoint_left.mpr (fun x hx hxS => hx (hSU hxS))
  obtain ⟨eta, hzero, hone, _⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, V)
      hU.isClosed_compl hS.isClosed hd (n := (⊤ : ℕ∞))
  have heta : ContDiff ℝ ∞ (eta : V → ℝ) := eta.contMDiff.contDiff
  have hsmooth : ContDiff ℝ ∞ (fun x => eta x • f x) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact heta.contDiffAt.smul (hf x hx)
    · apply (contDiffAt_const (c := (0 : W))).congr_of_eventuallyEq
      filter_upwards [hzero.filter_mono (nhds_le_nhdsSet hx)] with y hy
      simp only [hy, zero_smul]
  obtain ⟨O, hO, hSO, hOone⟩ := mem_nhdsSet_iff_exists.mp hone
  refine ⟨⟨fun x => eta x • f x, hsmooth.continuous⟩, hsmooth, O, hO, hSO, ?_⟩
  intro x hx
  change eta x • f x = f x
  rw [hOone hx, one_smul]

theorem exists_smooth_pointwise_extension
    {V W : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {U : Set V} (hU : IsOpen U) (f : V → W)
    (hf : ∀ x ∈ U, ContDiffAt ℝ ∞ f x)
    (u : C(K, V)) (hu : ∀ x, u x ∈ U) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ Phi : C(K, V) → C(K, W),
      ContDiff ℝ ∞ Phi ∧
      ∀ v : C(K, V), ‖v - u‖ < epsilon → ∀ x, Phi v x = f (v x) := by
  have hS : IsCompact (range u) := isCompact_range u.continuous
  obtain ⟨fExt, hfExt, O, hO, hSO, hEq⟩ :=
    exists_contDiff_extension_near_compact hS hU
      (by rintro _ ⟨x, rfl⟩; exact hu x) f hf
  obtain ⟨epsilon, hepsilon, hthick⟩ := hS.exists_thickening_subset_open hO hSO
  refine ⟨epsilon, hepsilon, fun v => fExt.comp v,
    ContinuousPathCompositionNative.contDiff_postcomp K fExt hfExt, ?_⟩
  intro v hv x
  apply hEq
  apply hthick
  apply mem_thickening_iff.mpr
  refine ⟨u x, mem_range_self x, ?_⟩
  simpa only [dist_eq_norm, ContinuousMap.sub_apply] using
    ((v - u).norm_coe_le_norm x).trans_lt hv

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

set_option backward.isDefEq.respectTransparency false in
theorem exists_smooth_jointChartStateSource_on_paths
    (u : C(K, ChartState (n := n) × ChartState (n := n)))
    (hB : ∀ x, (u x).1.1.PosDef) (hg : ∀ x, (u x).2.1.PosDef) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∃ Phi : C(K, ChartState (n := n) × ChartState (n := n)) →
        C(K, Matrix (Fin n) (Fin n) ℝ),
      ContDiff ℝ ∞ Phi ∧ ∀ v, ‖v - u‖ < epsilon → ∀ x,
        Phi v x = chartStateSource (chartStateJet (v x).1) (v x).2 := by
  let U : Set (ChartState (n := n) × ChartState (n := n)) :=
    {z | z.1.1.det ≠ 0 ∧ z.2.1.det ≠ 0}
  have hU : IsOpen U :=
    (isOpen_ne_fun continuous_fst.fst.matrix_det continuous_const).inter
      (isOpen_ne_fun continuous_snd.fst.matrix_det continuous_const)
  exact exists_smooth_pointwise_extension hU _
    (fun z hz => contDiffAt_jointChartStateSource_of_det_ne_zero z hz.1 hz.2) u
    (fun x => ⟨((u x).1.1.isUnit_iff_isUnit_det.mp (hB x).isUnit).ne_zero,
      ((u x).2.1.isUnit_iff_isUnit_det.mp (hg x).isUnit).ne_zero⟩)

set_option backward.isDefEq.respectTransparency false in
theorem exists_smooth_jointLowerJetSource_on_paths
    (u : C(K, ChartState (n := n) × MetricLowerJet n))
    (hB : ∀ x, (u x).1.1.PosDef) (hg : ∀ x, (u x).2.1.PosDef) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∃ Phi : C(K, ChartState (n := n) × MetricLowerJet n) →
        C(K, Matrix (Fin n) (Fin n) ℝ),
      ContDiff ℝ ∞ Phi ∧ ∀ v, ‖v - u‖ < epsilon → ∀ x,
        Phi v x = lowerJetSource (chartStateJet (v x).1) (v x).2 := by
  let U : Set (ChartState (n := n) × MetricLowerJet n) :=
    {z | z.1.1.det ≠ 0 ∧ z.2.1.det ≠ 0}
  have hU : IsOpen U :=
    (isOpen_ne_fun continuous_fst.fst.matrix_det continuous_const).inter
      (isOpen_ne_fun continuous_snd.fst.matrix_det continuous_const)
  exact exists_smooth_pointwise_extension hU _
    (fun z hz => contDiffAt_jointLowerJetSource_of_det_ne_zero z hz.1 hz.2) u
    (fun x => ⟨((u x).1.1.isUnit_iff_isUnit_det.mp (hB x).isUnit).ne_zero,
      ((u x).2.1.isUnit_iff_isUnit_det.mp (hg x).isUnit).ne_zero⟩)

set_option backward.isDefEq.respectTransparency false in
theorem exists_smooth_jointLowerPerturbationSource_on_paths
    (u : C(K, ChartState (n := n) × MetricLowerJet n))
    (hB : ∀ x, (u x).1.1.PosDef) (hg : ∀ x, (u x).2.1.PosDef) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∃ Phi : C(K, ChartState (n := n) × MetricLowerJet n) →
        C(K, Matrix (Fin n) (Fin n) ℝ),
      ContDiff ℝ ∞ Phi ∧ ∀ v, ‖v - u‖ < epsilon → ∀ x,
        Phi v x = lowerPerturbationSource (chartStateJet (v x).1) (v x).2 := by
  let U : Set (ChartState (n := n) × MetricLowerJet n) :=
    {z | z.1.1.det ≠ 0 ∧ z.2.1.det ≠ 0}
  have hU : IsOpen U :=
    (isOpen_ne_fun continuous_fst.fst.matrix_det continuous_const).inter
      (isOpen_ne_fun continuous_snd.fst.matrix_det continuous_const)
  exact exists_smooth_pointwise_extension hU _
    (fun z hz => contDiffAt_jointLowerPerturbationSource_of_det_ne_zero z hz.1 hz.2) u
    (fun x => ⟨((u x).1.1.isUnit_iff_isUnit_det.mp (hB x).isUnit).ne_zero,
      ((u x).2.1.isUnit_iff_isUnit_det.mp (hg x).isUnit).ne_zero⟩)

end CompactRangeRegularity

section ForcingCoefficientRegularity

open Set Filter Metric SpectralHeatNative TimeL2BilinearNative
open scoped Topology Matrix.Norms.Elementwise

variable {iota : Type*} [Countable iota] {T : ℝ}

def shiftedTraceOperator (hT : 0 ≤ T) (lambda : iota → NNReal) :
    ForcingSpace iota T →L[ℝ] ResponsePath iota T :=
  ((shiftedBaseMultiplier lambda).compLeftContinuous ℝ (Icc (0 : ℝ) T)).comp
      (responseOperator hT lambda) +
    ((shiftedTraceMultiplier lambda).compLeftContinuous ℝ (Icc (0 : ℝ) T)).comp
      (traceOperator hT lambda)

@[simp] theorem shiftedTraceOperator_apply (hT : 0 ≤ T) (lambda : iota → NNReal)
    (F : ForcingSpace iota T) :
    shiftedTraceOperator hT lambda F = shiftedTracePath hT lambda F := rfl

theorem norm_shiftedTraceOperator_le (hT : 0 ≤ T) (lambda : iota → NNReal) :
    ‖shiftedTraceOperator hT lambda‖ ≤ Real.sqrt T + 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact norm_shiftedTracePath_le hT lambda

def lowerJetContractionOperator : Matrix (Fin n) (Fin n) ℝ →L[ℝ]
    MetricSecondJet n →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  (LinearMap.mk₂ ℝ (lowerJetContraction (n := n))
    (by intro A B Q; ext i j
        simp only [lowerJetContraction, Matrix.add_apply, add_mul, Finset.sum_add_distrib])
    (by intro c A Q; ext i j
        simp only [lowerJetContraction, Matrix.smul_apply, smul_eq_mul,
          Finset.mul_sum, mul_assoc])
    lowerJetContraction_add_right
    (by intro c A Q; ext i j
        simp only [lowerJetContraction, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul,
          Finset.mul_sum]
        apply Finset.sum_congr rfl; intro a _
        apply Finset.sum_congr rfl; intro b _; ring)).mkContinuous₂
    ((n : ℝ) ^ 2) norm_lowerJetContraction_le

def spatialJetContraction : C(M, Matrix (Fin n) (Fin n) ℝ) →L[ℝ]
    Lp (MetricSecondJet n) 2 μ →L[ℝ] Lp (Matrix (Fin n) (Fin n) ℝ) 2 μ :=
  (lowerJetContractionOperator.holderL μ (⊤ : ENNReal) 2 2).comp
    (ContinuousMap.toLp (⊤ : ENNReal) μ ℝ)

set_option backward.isDefEq.respectTransparency false in
theorem spatialJetContraction_coe (A : C(M, Matrix (Fin n) (Fin n) ℝ))
    (Q : Lp (MetricSecondJet n) 2 μ) :
    spatialJetContraction μ A Q =ᵐ[μ] (fun x => lowerJetContraction (A x) (Q x)) := by
  filter_upwards [lowerJetContractionOperator.coeFn_holder (r := (2 : ENNReal))
    (ContinuousMap.toLp (⊤ : ENNReal) μ ℝ A) Q,
    ContinuousMap.coeFn_toLp (p := (⊤ : ENNReal)) (μ := μ) (𝕜 := ℝ) A] with x hx hA
  change spatialJetContraction μ A Q x =
    lowerJetContraction ((ContinuousMap.toLp (⊤ : ENNReal) μ ℝ A) x) (Q x) at hx
  rw [hA] at hx
  exact hx

set_option backward.isDefEq.respectTransparency false in

theorem exists_smooth_principal_forcing_extension (hT : 0 ≤ T)
    (u : TimePath C(M, ChartState (n := n) × MetricLowerJet n) T)
    (hB : ∀ t x, (u t x).1.1.PosDef) (hg : ∀ t x, (u t x).2.1.PosDef) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∃ Phi : (TimePath C(M, ChartState (n := n) × MetricLowerJet n) T ×
        TimeL2 (Lp (MetricSecondJet n) 2 μ) T) →
        TimeL2 (Lp (Matrix (Fin n) (Fin n) ℝ) 2 μ) T,
      ContDiff ℝ ∞ Phi ∧ ∀ v, ‖v - u‖ < epsilon →
        ∀ Q : TimeL2 (Lp (MetricSecondJet n) 2 μ) T,
        ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T,
          Phi (v, Q) t =ᵐ[μ] (fun x => lowerJetContraction
            ((v ⟨t, ht⟩ x).2.1⁻¹ - (v ⟨t, ht⟩ x).1.1⁻¹) (Q t x)) := by
  let V := ChartState (n := n) × MetricLowerJet n
  let U : Set V := {z | z.1.1.det ≠ 0 ∧ z.2.1.det ≠ 0}
  let f : V → Matrix (Fin n) (Fin n) ℝ := fun z => z.2.1⁻¹ - z.1.1⁻¹
  have hU : IsOpen U :=
    (isOpen_ne_fun continuous_fst.fst.matrix_det continuous_const).inter
      (isOpen_ne_fun continuous_snd.fst.matrix_det continuous_const)
  have hf (z : V) (hz : z ∈ U) : ContDiffAt ℝ ∞ f z := by
    have hcurrent : ContDiffAt ℝ ∞ (fun q : V => matrixInverseEntries q.2.1) z :=
      (contDiffAt_matrixInverseEntries_infty _ hz.2).comp
        (f := fun q : V => q.2.1) (g := matrixInverseEntries) z (by fun_prop)
    have hbackground : ContDiffAt ℝ ∞ (fun q : V => matrixInverseEntries q.1.1) z :=
      (contDiffAt_matrixInverseEntries_infty _ hz.1).comp
        (f := fun q : V => q.1.1) (g := matrixInverseEntries) z (by fun_prop)
    exact hcurrent.sub hbackground
  have hS : IsCompact (range u.uncurry) := isCompact_range u.uncurry.continuous
  obtain ⟨fExt, hfExt, O, hO, hSO, hEq⟩ := exists_contDiff_extension_near_compact hS hU
    (by rintro _ ⟨⟨t, x⟩, rfl⟩
        exact ⟨((u t x).1.1.isUnit_iff_isUnit_det.mp (hB t x).isUnit).ne_zero,
          ((u t x).2.1.isUnit_iff_isUnit_det.mp (hg t x).isUnit).ne_zero⟩) f hf
  obtain ⟨epsilon, hepsilon, hthick⟩ := hS.exists_thickening_subset_open hO hSO
  let G : C(C(M, V), C(M, Matrix (Fin n) (Fin n) ℝ)) :=
    ⟨fun v => fExt.comp v, fExt.continuous_postcomp⟩
  have hG : ContDiff ℝ ∞ G :=
    ContinuousPathCompositionNative.contDiff_postcomp M fExt hfExt
  let coefficient : TimePath C(M, V) T → TimePath C(M, Matrix (Fin n) (Fin n) ℝ) T :=
    fun v => G.comp v
  have hcoefficient : ContDiff ℝ ∞ coefficient :=
    ContinuousPathCompositionNative.contDiff_postcomp (Icc (0 : ℝ) T) G hG
  let B := productOperator hT (spatialJetContraction (n := n) μ)
  refine ⟨epsilon, hepsilon, fun z => B (coefficient z.1) z.2,
    (B.contDiff.comp (hcoefficient.comp contDiff_fst)).clm_apply contDiff_snd, ?_⟩
  intro v hv Q
  filter_upwards [product_ae_eq_on_interval hT (spatialJetContraction (n := n) μ)
    (coefficient v) Q] with t ht
  intro htmem
  change B (coefficient v) Q t =ᵐ[μ] _
  rw [show B (coefficient v) Q t = spatialJetContraction μ
    (coefficient v ⟨t, htmem⟩) (Q t) from ht htmem]
  filter_upwards [spatialJetContraction_coe μ (coefficient v ⟨t, htmem⟩) (Q t)] with x hx
  rw [hx]
  change lowerJetContraction (fExt (v ⟨t, htmem⟩ x)) (Q t x) = _
  rw [hEq (hthick (mem_thickening_iff.mpr
    ⟨u ⟨t, htmem⟩ x,
      mem_range_self (f := u.uncurry) ((⟨t, htmem⟩ : Icc (0 : ℝ) T), x), by
      rw [dist_eq_norm]
      exact ((v ⟨t, htmem⟩ - u ⟨t, htmem⟩).norm_coe_le_norm x).trans_lt
        (((v - u).norm_coe_le_norm ⟨t, htmem⟩).trans_lt hv)⟩))]

end ForcingCoefficientRegularity

end DeTurckMetricProducerNative

end PoincareConjecture
