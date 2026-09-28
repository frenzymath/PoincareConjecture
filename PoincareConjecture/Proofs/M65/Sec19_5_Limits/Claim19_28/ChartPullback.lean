import PoincareConjecture.Proofs.M62.Sec19_1_PullbackCurvature
import PoincareConjecture.Proofs.M09.CompactFieldExtension








set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




theorem m65Pullback_hasDerivAt_coordinates {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (p : M) {gamma : ℝ → M}
    {Y : ∀ y, TangentSpace (𝓡 n) (gamma y)}
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ gamma)
    (hY : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n).tangent ∞
      (fun y => (⟨gamma y, Y y⟩ : TangentBundle (𝓡 n) M)))
    {x : ℝ} (hx : gamma x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    HasDerivAt (F := EuclideanSpace ℝ (Fin n)) (fun y => mfderiv (𝓡 n) (𝓡 n)
      (chartAt (EuclideanSpace ℝ (Fin n)) p) (gamma y) (Y y))
      (let L : TangentSpace (𝓡 n) (gamma x) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
        mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p) (gamma x)
       L (rampHorizontalCovariantDerivative D gamma Y x) -
        M04.shiChartChristoffel D (chartAt (EuclideanSpace ℝ (Fin n)) p)
          ((chartAt (EuclideanSpace ℝ (Fin n)) p) (gamma x))
          (L (curveVelocity (n := n) gamma x)) (L (Y x))) x := by
  let E := EuclideanSpace ℝ (Fin n)
  let e := chartAt E p
  let U := gamma ⁻¹' e.source
  have hU : IsOpen U := e.open_source.preimage hgamma.continuous
  let v : ℝ → E := fun y => mfderiv (𝓡 n) (𝓡 n) e (gamma y) (Y y)
  have hv : ContDiffOn ℝ ∞ v U :=
    ((Proofs.M09.tangentChartPhase_contMDiffOn p).comp hY.contMDiffOn
      (fun y (hy : y ∈ U) => hy)).contDiffOn.snd
  have hcongr : rampHorizontalCovariantDerivative D gamma Y x =
      rampHorizontalCovariantDerivative D gamma
        (fun y => Proofs.M09.chartVectorField p (v y) (gamma y)) x := by
    apply M62.pullback_congr
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (Proofs.M09.chartVectorField_differential p (gamma y) (Y y) hy).symm
  have hcoord := M62.pullback_chart_field_coordinates D p
    (hgamma.mdifferentiableAt (by simp)) hx hU hx v hv
  rw [← hcongr] at hcoord
  apply ((hv.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasDerivAt.congr_deriv
  exact eq_sub_of_add_eq hcoord.symm

end PoincareConjecture
