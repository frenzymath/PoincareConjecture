import PoincareLib.Geometry.CurveShortening.Deformation.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.HessianTransport
import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.Conformal.ConnectionTrace

/-!
# The actual connection defect and its disk trace

The genuine frozen pullback Hessian minus the lifted source connection
agrees with the second fundamental form in the actual chart.
Source: Morgan--Tian Lemma 19.2, printed p. 438;
M65 derivation 24, twelfth stage.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareMT

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {h : RiemannianMetric 2 LoopPlane}

/-- The genuine ambient Hessian minus the lifted actual source connection.
Source: MT Lemma 19.2, p. 438; derivation 24, twelfth stage. -/
noncomputable def m65PlaneSecondFundamentalForm (D : LeviCivitaData g)
    (Ds : LeviCivitaData h) (f : LoopPlane → M) (x u v : LoopPlane) :
    TangentSpace (𝓡 n) (f x) :=
  m65PlaneHessian D f x u v -
    mfderiv (𝓡 2) (𝓡 n) f x (M65Gauss.connectionCoefficient Ds x u v)

/-- The actual connection defect agrees with the pushed coordinate second
fundamental form. Source: MT Lemma 19.2, p. 438; derivation 24. -/
theorem m65PlaneSecondFundamentalForm_chart
    (D : LeviCivitaData g) (Ds : LeviCivitaData h)
    {gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (DE : LeviCivitaData gE) (p : M)
    {f : LoopPlane → M} {U : Set LoopPlane} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) ∞ f U) {x : LoopPlane} (hx : x ∈ U)
    (hsource : f x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (hmetric : ∀ᶠ y in 𝓝 ((chartAt (EuclideanSpace ℝ (Fin n)) p) (f x)),
      ∀ a b : EuclideanSpace ℝ (Fin n),
        gE.inner y a b = g.inner ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm y)
          (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p).symm y a)
          (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p).symm y b))
    (u v : LoopPlane) :
    m65PlaneSecondFundamentalForm D Ds f x u v =
      mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p).symm
        ((chartAt (EuclideanSpace ℝ (Fin n)) p) (f x))
        (M65Gauss.secondFundamentalForm DE Ds
          ((chartAt (EuclideanSpace ℝ (Fin n)) p) ∘ f) x u v) := by
  let c := chartAt (EuclideanSpace ℝ (Fin n)) p
  have hfx := ((hf x hx).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hdf (a : LoopPlane) : mfderiv (𝓡 2) (𝓡 n) f x a =
      mfderiv (𝓡 n) (𝓡 n) c.symm (c (f x)) (fderiv ℝ (c ∘ f) x a) := by
    rw [← m65PlaneDerivative_chart p hfx hsource a]
    have he := Proofs.M09.chartVectorField_at_inverse p
      (fderiv ℝ (c ∘ f) x a) (c (f x)) (c.map_source hsource)
    rw [show (chartAt (EuclideanSpace ℝ (Fin n)) p).symm (c (f x)) = f x from
      c.left_inv hsource] at he
    exact he
  unfold m65PlaneSecondFundamentalForm
  rw [M65Gauss.planeHessian_chart D DE p hU hf hx hsource hmetric, hdf]
  simpa +instances only [M65Gauss.secondFundamentalForm, c] using!
    ((mfderiv (𝓡 n) (𝓡 n) c.symm (c (f x))).map_sub
      (M65Gauss.covariantHessianMap DE (c ∘ f) x u v)
      (fderiv ℝ (c ∘ f) x (M65Gauss.connectionCoefficient Ds x u v))).symm

/-- In genuine conformal source coordinates, the actual connection defect's
Euclidean trace is exactly the frozen harmonic tension. Source: MT Lemma
19.2, p. 438; derivation 24, twelfth stage. -/
theorem m65PlaneSecondFundamentalForm_euclideanTrace
    (D : LeviCivitaData g) (Ds : LeviCivitaData h)
    (f : LoopPlane → M) {x : LoopPlane} {c : LoopPlane → ℝ}
    (hconf : ∀ᶠ y in 𝓝 x, ∀ i j : Fin 2,
      h.inner y (EuclideanSpace.basisFun (Fin 2) ℝ i)
        (EuclideanSpace.basisFun (Fin 2) ℝ j) = if i = j then c y else 0) :
    (∑ i : Fin 2, m65PlaneSecondFundamentalForm D Ds f x
      (EuclideanSpace.basisFun (Fin 2) ℝ i)
      (EuclideanSpace.basisFun (Fin 2) ℝ i)) = m65PlaneTension D f x := by
  simp only [m65PlaneSecondFundamentalForm, Finset.sum_sub_distrib,
    ← map_sum, M65Gauss.connectionCoefficient_trace_eq_zero Ds hconf, map_zero, sub_zero]
  exact (m65PlaneTension_eq_hessianTrace D f x).symm

end PoincareMT
