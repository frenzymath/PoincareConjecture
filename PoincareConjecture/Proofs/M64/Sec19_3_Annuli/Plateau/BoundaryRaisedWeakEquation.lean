import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryVectorCoefficientTests
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryInverseMetric
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryComponentPairings

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff
open Poincare.Analysis.Sobolev.Weak

namespace PoincareConjecture

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

set_option maxHeartbeats 1200000 in

theorem m64WeightedMixedMetric_raised_equation
    {O S : Set LoopPlane} (hO : IsOpen O) (hS : MeasurableSet S)
    (hSO : S ⊆ O) (hSpos : ∀ p ∈ S, 0 < p 1)
    {u : LoopPlane → E} (hu : Continuous u)
    {V : Fin 2 → LoopPlane → E} (hV : ∀ i, MemLp (V i) 2 volume)
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => V i p j) (fun p => u p j) univ)
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hmap : MapsTo u O K)
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} (hG : ContDiffOn ℝ ∞ G U)
    (hpos : ∀ z ∈ U, ∀ v : E, v ≠ 0 → 0 < G z v v)
    (hsym : ∀ z ∈ U, ∀ v v' : E, G z v v' = G z v' v)
    (haxis : ∀ p ∈ O, p 1 = 0 → ∀ z : E,
      G (u p) (EuclideanSpace.single 0 1) z =
        G (u p) (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) * z 0)
    (w : Fin 2 → ℝ) (b : Fin (n + 1) → LoopPlane → ℝ)
    (hflux : ∀ j i, MemLp
      (fun p => w i * G (u p) (V i p) (EuclideanSpace.single j 1))
        2 (volume.restrict S))
    (hsource : ∀ j, IntegrableOn (b j) S)
    (heq : ∀ j, ∀ psi : LoopPlane → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ O → (j ≠ 0 → ∀ p : LoopPlane, p 1 = 0 → psi p = 0) →
      (∫ p, ∑ i : Fin 2, S.indicator
        (fun q => w i * G (u q) (V i q) (EuclideanSpace.single j 1)) p *
          fderiv ℝ psi p (EuclideanSpace.single i 1)) =
        ∫ p, S.indicator (b j) p * psi p)
    (k : Fin (n + 1)) {phi : LoopPlane → ℝ}
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ O)
    (hz : k ≠ 0 → ∀ p : LoopPlane, p 1 = 0 → phi p = 0) :
    (∫ p in S, ∑ i : Fin 2, w i * V i p k *
      fderiv ℝ phi p (EuclideanSpace.single i 1)) =
        ∫ p in S, phi p *
          ((∑ j : Fin (n + 1), b j p *
            (m64BoundaryMetricInverse (G (u p)) (EuclideanSpace.single k 1)) j) -
          ∑ i : Fin 2, ∑ j : Fin (n + 1),
            (w i * G (u p) (V i p) (EuclideanSpace.single j 1)) *
              fderiv ℝ (fun z =>
                (m64BoundaryMetricInverse (G z) (EuclideanSpace.single k 1)) j)
                  (u p) (V i p)) := by
  classical
  let f : Fin (n + 1) → E → ℝ := fun j z =>
    (m64BoundaryMetricInverse (G z) (EuclideanSpace.single k 1)) j
  have hQ : ContDiffOn ℝ ∞
      (fun z => m64BoundaryMetricInverse (G z) (EuclideanSpace.single k 1)) U :=
    (m64BoundaryMetricInverse_smooth hG hpos).clm_apply contDiffOn_const
  have hf (j : Fin (n + 1)) : ContDiffOn ℝ 1 (f j) U :=
    ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp_contDiffOn hQ).of_le (by simp)
  let F := fun j i => S.indicator
    (fun p => w i * G (u p) (V i p) (EuclideanSpace.single j 1))
  let B := fun j => S.indicator (b j)
  have hF (j : Fin (n + 1)) (i : Fin 2) : MemLp (F j i) 2 volume :=
    (memLp_indicator_iff_restrict hS).mpr (hflux j i)
  have hB (j : Fin (n + 1)) : Integrable (B j) :=
    (integrable_indicator_iff hS).mpr (hsource j)
  have hnot (p : LoopPlane) (hp0 : p 1 ≤ 0) : p ∉ S :=
    fun hpS => (not_lt.mpr hp0) (hSpos p hpS)
  have hface (j : Fin (n + 1)) (hj : j ≠ 0) (p : LoopPlane) (hp0 : p 1 = 0) :
      phi p * f j (u p) = 0 := by
    by_cases hpt : p ∈ tsupport phi
    · by_cases hk : k = 0
      · have hcol := m64BoundaryMetricInverse_tangent_column (G (u p))
          (hpos (u p) (hKU (hmap (hs hpt)))) (haxis p (hs hpt) hp0)
        simp only [f, hk, hcol, PiLp.smul_apply, PiLp.single_apply,
          hj, ite_false, smul_zero, mul_zero]
      · rw [hz hk p hp0, zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport hpt, zero_mul]
  have hh := m64NaturalGrowth_compact_vector_face_test
    (fun j : Fin (n + 1) => j ≠ 0) hO hF hB
    (fun j i p hp0 => indicator_of_notMem (hnot p hp0) _)
    (fun j p hp0 => indicator_of_notMem (hnot p hp0) _)
    hu hV hw hU hK hKU hmap hf hp hc hs hs hface heq
  have hpair (p : LoopPlane) (hpS : p ∈ S) (i : Fin 2) :
      (∑ j : Fin (n + 1), F j i p * f j (u p)) = w i * V i p k := by
    simp only [F, f, indicator_of_mem hpS, mul_assoc, ← Finset.mul_sum,
      M60.suCoordinateDual_pairing]
    rw [m64BoundaryMetricInverse_pairing (G (u p))
      (hpos (u p) (hKU (hmap (hSO hpS))))
      (hsym (u p) (hKU (hmap (hSO hpS))))]
    simp only [EuclideanSpace.inner_single_right, starRingEnd_apply, star_trivial, one_mul]
  have hleft : (fun p => ∑ i : Fin 2, (∑ j : Fin (n + 1), F j i p * f j (u p)) *
      fderiv ℝ phi p (EuclideanSpace.single i 1)) =
        S.indicator (fun p => ∑ i : Fin 2, w i * V i p k *
          fderiv ℝ phi p (EuclideanSpace.single i 1)) := by
    funext p
    by_cases hpS : p ∈ S
    · simp only [indicator_of_mem hpS, hpair p hpS]
    · simp only [F, indicator_of_notMem hpS, zero_mul, Finset.sum_const_zero]
  have hright : (fun p => phi p * ((∑ j : Fin (n + 1), B j p * f j (u p)) -
      ∑ i : Fin 2, ∑ j : Fin (n + 1), F j i p * fderiv ℝ (f j) (u p) (V i p))) =
        S.indicator (fun p => phi p * ((∑ j : Fin (n + 1), b j p * f j (u p)) -
          ∑ i : Fin 2, ∑ j : Fin (n + 1),
            (w i * G (u p) (V i p) (EuclideanSpace.single j 1)) *
              fderiv ℝ (f j) (u p) (V i p))) := by
    funext p
    by_cases hpS : p ∈ S
    · simp only [F, B, indicator_of_mem hpS]
    · simp only [F, B, indicator_of_notMem hpS, zero_mul,
        Finset.sum_const_zero, sub_self, mul_zero]
  rw [hleft, hright, integral_indicator hS, integral_indicator hS] at hh
  exact hh

end PoincareConjecture
