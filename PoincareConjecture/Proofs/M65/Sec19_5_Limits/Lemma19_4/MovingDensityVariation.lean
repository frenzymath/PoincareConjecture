import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.DensityVariation
import PoincareConjecture.Proofs.M62.Sec19_1_MetricVariation
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Icc a b))




noncomputable def m65PlaneMotionDensity (u : ℝ → LoopPlane → M)
    (t : ℝ) (z : LoopPlane) : ℝ :=
  let e : (s : ℝ) → Fin 2 → TangentSpace (𝓡 n) (u s z) := fun s i =>
    mfderiv (𝓡 2) (𝓡 n) (u s) z (EuclideanSpace.basisFun (Fin 2) ℝ i)
  let A : Fin 2 → TangentSpace (𝓡 n) (u t z) := fun i =>
    rampHorizontalCovariantDerivative (F.connection t) (fun s => u s z)
      (fun s => e s i) t
  let B : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
    (F.metric t).inner (u t z) (A i) (e t j) +
      (F.metric t).inner (u t z) (e t i) (A j)
  let G := m60AreaGram (F.metric t) (u t) z
  if G.det = 0 then 0
  else (1 / 2 : ℝ) * Matrix.trace (G⁻¹ * B) * m60AreaDensity (F.metric t) (u t) z




theorem m65MovingAreaDensity_hasDerivAt (u : ℝ → LoopPlane → M)
    (z : LoopPlane) {t : ℝ} (ht : t ∈ Ioo a b)
    (hu : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) (fun s => u s z) t)
    (hcol : ∀ i : Fin 2, MDifferentiableAt (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n))
      (fun s => (⟨u s z, mfderiv (𝓡 2) (𝓡 n) (u s) z
        (EuclideanSpace.basisFun (Fin 2) ℝ i)⟩ : TangentBundle (𝓡 n) M)) t)
    (hpos : 0 < (m60AreaGram (F.metric t) (u t) z).det) :
    HasDerivAt (fun s => m60AreaDensity (F.metric s) (u s) z)
      (-m65PlaneRicciTraceDensity (F.connection t) (u t) z +
        m65PlaneMotionDensity F u t z) t := by
  let e : (s : ℝ) → Fin 2 → TangentSpace (𝓡 n) (u s z) := fun s i =>
    mfderiv (𝓡 2) (𝓡 n) (u s) z (EuclideanSpace.basisFun (Fin 2) ℝ i)
  let A : Fin 2 → TangentSpace (𝓡 n) (u t z) := fun i =>
    rampHorizontalCovariantDerivative (F.connection t) (fun s => u s z)
      (fun s => e s i) t
  let B : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
    (F.metric t).inner (u t z) (A i) (e t j) +
      (F.metric t).inner (u t z) (e t i) (A j)
  let R : Matrix (Fin 2) (Fin 2) ℝ :=
    fun i j => (F.connection t).ricci (u t z) (e t i) (e t j)
  let G : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun s => m60AreaGram (F.metric s) (u s) z
  have hG (i j : Fin 2) : HasDerivAt (fun s => G s i j)
      (((-2 : ℝ) • R + B) i j) t := by
    have h := M62.hasDerivAt_flow_metric_pairing F ht hu (hcol i) (hcol j)
    change HasDerivAt (fun s => (F.metric s).inner (u s z) (e s i) (e s j))
      (-2 * R i j + B i j) t
    exact h.congr_deriv (by dsimp only [R, B, A, e]; ring)
  have h := Poincare.Matrix.hasDerivAt_sqrt_det_eq_half_trace_inv_mul
    G ((-2 : ℝ) • R + B) t hG hpos
  have hfun : (fun s => m60AreaDensity (F.metric s) (u s) z) =
      fun s => Real.sqrt (G s).det := by
    funext s
    exact congrArg Real.sqrt (max_eq_right (m65AreaGram_det_nonneg (F.metric s) (u s) z))
  rw [hfun]
  convert h using 1
  simp only [m65PlaneRicciTraceDensity, m65PlaneMotionDensity, if_neg hpos.ne',
    mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul,
    m60AreaDensity, max_eq_right (m65AreaGram_det_nonneg (F.metric t) (u t) z)]
  change -(Matrix.trace ((G t)⁻¹ * R) * Real.sqrt (G t).det) +
    (1 / 2 : ℝ) * Matrix.trace ((G t)⁻¹ * B) * Real.sqrt (G t).det = _
  ring

set_option maxHeartbeats 1000000 in




theorem m65MovingAreaDensity_hasDerivAt_of_contMDiffAt
    (u : ℝ → LoopPlane → M) (z : LoopPlane) {t : ℝ} (ht : t ∈ Ioo a b)
    (hu : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 n) 2
      (Function.uncurry u) (t, z))
    (hpos : 0 < (m60AreaGram (F.metric t) (u t) z).det) :
    HasDerivAt (fun s => m60AreaDensity (F.metric s) (u s) z)
      (-m65PlaneRicciTraceDensity (F.connection t) (u t) z +
        m65PlaneMotionDensity F u t z) t := by
  have hbase : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓡 n) 1 (fun s => u s z) t :=
    (hu.of_le (by norm_num)).comp t (contMDiffAt_id.prodMk contMDiffAt_const)
  apply m65MovingAreaDensity_hasDerivAt F u z ht (hbase.mdifferentiableAt (by decide))
    _ hpos
  intro i
  have hcoord := hu.mfderiv u (fun _ : ℝ => z) (m := 1)
    contMDiffAt_const (by norm_num)
  have hv : ContMDiffAt (𝓘(ℝ, ℝ)) ((𝓡 2).prod (𝓡 2)) 1
      (fun _ : ℝ => (⟨z, EuclideanSpace.basisFun (Fin 2) ℝ i⟩ :
        TangentBundle (𝓡 2) LoopPlane)) t := contMDiffAt_const
  have hcolumn : ContMDiffAt (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) 1
      (fun s => (⟨u s z, mfderiv (𝓡 2) (𝓡 n) (u s) z
        (EuclideanSpace.basisFun (Fin 2) ℝ i)⟩ : TangentBundle (𝓡 n) M)) t :=
    ContMDiffAt.clm_apply_of_inCoordinates
      (IB₁ := 𝓡 2) (IB₂ := 𝓡 n) (IM := 𝓘(ℝ, ℝ))
      (E₁ := TangentSpace (𝓡 2)) (E₂ := TangentSpace (𝓡 n))
      (b₁ := fun _ : ℝ => z) (b₂ := fun s => u s z)
      (ϕ := fun s => mfderiv (𝓡 2) (𝓡 n) (u s) z)
      (v := fun _ => EuclideanSpace.basisFun (Fin 2) ℝ i) hcoord hv hbase
  exact hcolumn.mdifferentiableAt (by decide)

end PoincareConjecture
