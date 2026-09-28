import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryMetricSource
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryRaisedWeakEquation










set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff ENNReal
open Poincare.Analysis.Sobolev.Weak

namespace PoincareConjecture

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace





theorem m64WeightedMixedMetric_raised_quadratic_system
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
    (w : Fin 2 → ℝ)
    (heq : ∀ j : Fin (n + 1), ∀ psi : LoopPlane → ℝ,
      ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ O →
      (j ≠ 0 → ∀ p : LoopPlane, p 1 = 0 → psi p = 0) →
      (∫ p, ∑ i : Fin 2, S.indicator
        (fun q => w i * G (u q) (V i q) (EuclideanSpace.single j 1)) p *
          fderiv ℝ psi p (EuclideanSpace.single i 1)) =
        ∫ p, S.indicator (fun q => m64WeightedQuadraticSource w (fderiv ℝ G (u q))
          (V 0 q, V 1 q) (EuclideanSpace.single j 1)) p * psi p) :
    let b := fun j p => m64WeightedQuadraticSource w (fderiv ℝ G (u p))
      (V 0 p, V 1 p) (EuclideanSpace.single j 1)
    let B := fun k p => m64BoundaryRaisedSource G w (u p)
      (fun i => V i p) (fun j => b j p) k
    ∃ C : ℝ, 0 ≤ C ∧ (∀ k, IntegrableOn (B k) S) ∧
      (∀ k, ∀ᵐ p ∂volume.restrict S,
        |B k p| ≤ C * ∑ j : Fin (n + 1), ∑ i : Fin 2, (V i p j) ^ 2) ∧
      ∀ k, ∀ phi : LoopPlane → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
        tsupport phi ⊆ O → (k ≠ 0 → ∀ p : LoopPlane, p 1 = 0 → phi p = 0) →
        (∫ p in S, ∑ i : Fin 2, w i * V i p k *
          fderiv ℝ phi p (EuclideanSpace.single i 1)) =
            ∫ p in S, phi p * B k p := by
  let b := fun j p => m64WeightedQuadraticSource w (fderiv ℝ G (u p))
    (V 0 p, V 1 p) (EuclideanSpace.single j 1)
  have hmapS : MapsTo u S K := fun _ hp => hmap (hSO hp)
  have hVS (i : Fin 2) : MemLp (V i) 2 (volume.restrict S) := (hV i).restrict S
  have hb : ∀ j, IntegrableOn (b j) S :=
    m64WeightedMetricSource_integrable hS hU hK hKU hG w hu.continuousOn hmapS hVS
  obtain ⟨L, hL⟩ := hK.exists_bound_of_continuousOn (hG.continuousOn.mono hKU)
  have hGM : MemLp (fun p => G (u p)) ⊤ (volume.restrict S) :=
    memLp_top_of_bound (((hG.continuousOn.mono hKU).comp hu.continuousOn hmapS
      ).aestronglyMeasurable hS) L (by
        filter_upwards [ae_restrict_mem hS] with p hp
        exact hL (u p) (hmapS hp))
  have hflux (j : Fin (n + 1)) (i : Fin 2) : MemLp
      (fun p => w i * G (u p) (V i p) (EuclideanSpace.single j 1)) 2
        (volume.restrict S) := by
    have hGV := (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) («E» := E)).memLp_of_bilin
      (p := 2) (q := ⊤) 2 (hVS i) hGM
    exact (((ContinuousLinearMap.apply ℝ ℝ («E» := E))
      (EuclideanSpace.single j 1)).comp_memLp' hGV).const_mul _
  obtain ⟨C, hC, hdata⟩ := m64BoundaryMetricRaisedSource_data
    hS hU hK hKU hG hpos w hu.continuousOn hmapS hVS
  refine ⟨C, hC, fun k => (hdata k).1, fun k => (hdata k).2, ?_⟩
  intro k phi hp hc hs hz
  exact m64WeightedMixedMetric_raised_equation hO hS hSO hSpos hu hV hw
    hU hK hKU hmap hG hpos hsym haxis w b hflux hb heq k hp hc hs hz

end PoincareConjecture
