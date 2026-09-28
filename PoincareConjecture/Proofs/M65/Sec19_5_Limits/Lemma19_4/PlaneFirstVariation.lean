import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.ConformalVariation
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.PlaneTorsion
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.PlaneTimeField
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.Pullback











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



noncomputable def m65PlaneTension {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (f : LoopPlane → M) (z : LoopPlane) :
    TangentSpace (𝓡 n) (f z) :=
  ∑ i : Fin 2, rampHorizontalCovariantDerivative D
    (fun r => f (z + r • EuclideanSpace.basisFun (Fin 2) ℝ i))
    (fun r => mfderiv (𝓡 2) (𝓡 n) f (z + r • EuclideanSpace.basisFun (Fin 2) ℝ i)
      (EuclideanSpace.basisFun (Fin 2) ℝ i)) 0



noncomputable def m65PlaneVariationFlux (g : RiemannianMetric n M)
    (u : ℝ → LoopPlane → M) (t : ℝ) (i : Fin 2) (z : LoopPlane) : ℝ :=
  g.inner (u t z) (curveVelocity (fun s => u s z) t)
    (mfderiv (𝓡 2) (𝓡 n) (u t) z (EuclideanSpace.basisFun (Fin 2) ℝ i))

variable {a b : ℝ} (F : RicciFlow n M (Icc a b))

set_option maxHeartbeats 1500000 in



theorem m65PlaneMotionDensity_eq_divergence_sub_tension
    (u : ℝ → LoopPlane → M) {U : Set (ℝ × LoopPlane)} (hU : IsOpen U)
    (hu : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 n) ∞ (Function.uncurry u) U)
    {t : ℝ} {z : LoopPlane} (htz : (t, z) ∈ U) (c : ℝ)
    (hconf : m60AreaGram (F.metric t) (u t) z = c • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    m65PlaneMotionDensity F u t z =
      (∑ i : Fin 2, deriv (fun r : ℝ => m65PlaneVariationFlux (F.metric t) u t i
        (z + r • EuclideanSpace.basisFun (Fin 2) ℝ i)) 0) -
      (F.metric t).inner (u t z) (curveVelocity (fun s => u s z) t)
        (m65PlaneTension (F.connection t) (u t) z) := by
  let v : Fin 2 → LoopPlane := EuclideanSpace.basisFun (Fin 2) ℝ
  let V : (w : LoopPlane) → TangentSpace (𝓡 n) (u t w) :=
    fun w => curveVelocity (fun s => u s w) t
  let e : (w : LoopPlane) → Fin 2 → TangentSpace (𝓡 n) (u t w) :=
    fun w i => mfderiv (𝓡 2) (𝓡 n) (u t) w (v i)
  let A : Fin 2 → TangentSpace (𝓡 n) (u t z) := fun i =>
    rampHorizontalCovariantDerivative (F.connection t) (fun s => u s z)
      (fun s => mfderiv (𝓡 2) (𝓡 n) (u s) z (v i)) t
  let L : Fin 2 → TangentSpace (𝓡 n) (u t z) := fun i =>
    rampHorizontalCovariantDerivative (F.connection t) (fun r => u t (z + r • v i))
      (fun r => e (z + r • v i) i) 0
  have hjoint := (hu (t, z) htz).contMDiffAt (hU.mem_nhds htz)
  have hf : ContMDiffAt (𝓡 2) (𝓡 n) ∞ (u t) z :=
    hjoint.comp z (contMDiffAt_const.prodMk contMDiffAt_id)
  have hV : MDifferentiableAt (𝓡 2) ((𝓡 n).prod (𝓡 n))
      (fun w => (⟨u t w, V w⟩ : TangentBundle (𝓡 n) M)) z :=
    (m65PlaneTimeVelocity_contMDiffAt u (hjoint.of_le (by decide))).mdifferentiableAt
      (by decide)
  have he (i : Fin 2) : MDifferentiableAt (𝓡 2) ((𝓡 n).prod (𝓡 n))
      (fun w => (⟨u t w, e w i⟩ : TangentBundle (𝓡 n) M)) z :=
    (RiemannianMetric.contMDiffAt_mfderiv_const_vector hf (v i)).mdifferentiableAt (by simp)
  have hpair (i : Fin 2) :
      deriv (fun r : ℝ => m65PlaneVariationFlux (F.metric t) u t i (z + r • v i)) 0 =
        (F.metric t).inner (u t z) (A i) (e z i) +
          (F.metric t).inner (u t z) (V z) (L i) := by
    have hline : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 2)
        (fun r : ℝ => z + r • v i) 0 :=
      ((differentiableAt_const z).add (differentiableAt_id.smul_const (v i))).mdifferentiableAt
    have hf' : MDifferentiableAt (𝓡 2) (𝓡 n) (u t) (z + (0 : ℝ) • v i) := by
      simpa only [zero_smul, add_zero] using hf.mdifferentiableAt (by simp)
    have hV' : MDifferentiableAt (𝓡 2) ((𝓡 n).prod (𝓡 n))
        (fun w => (⟨u t w, V w⟩ : TangentBundle (𝓡 n) M)) (z + (0 : ℝ) • v i) := by
      simpa only [zero_smul, add_zero] using hV
    have he' : MDifferentiableAt (𝓡 2) ((𝓡 n).prod (𝓡 n))
        (fun w => (⟨u t w, e w i⟩ : TangentBundle (𝓡 n) M)) (z + (0 : ℝ) • v i) := by
      simpa only [zero_smul, add_zero] using he i
    have h := M62.hasDerivAt_metric_pairing (F.connection t)
      (hf'.comp 0 hline) (hV'.comp 0 hline) (he'.comp 0 hline)
    have hcomm := m65PlaneCovariantColumn_commute (F.connection t) u hU hu htz (v i)
    have hpoint : z + (0 : ℝ) • v i = z := by simp
    have hd := h.deriv
    dsimp only [Function.comp_def] at hd
    rw [hpoint] at hd
    simpa only [← hcomm, m65PlaneVariationFlux, V, e, A, L, v] using hd
  rw [m65PlaneMotionDensity_eq_sum_of_conformal F u t z c hconf]
  change (∑ i, (F.metric t).inner (u t z) (A i) (e z i)) =
    (∑ i, deriv (fun r : ℝ => m65PlaneVariationFlux (F.metric t) u t i (z + r • v i)) 0) -
      (F.metric t).inner (u t z) (V z) (∑ i, L i)
  simp only [hpair, Finset.sum_add_distrib, map_sum]
  ring

end PoincareConjecture
