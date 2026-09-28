import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.VectorNorm
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.LocalFinite
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.TraceRegularity

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter Bundle
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem contMDiff_inner_connection (D : LeviCivitaData g)
    {V Z : (x : M) → TangentSpace (𝓡 n) x}
    (hV : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% V))
    (hZ : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z)) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => ∑ i,
      g.inner x (D.connection V x (g.orthonormalBasis x i))
        (D.connection Z x (g.orthonormalBasis x i))) := by
  let T : CovariantTensorEvaluation n M 2 := fun x v =>
    g.inner x (D.connection V x (v 0)) (D.connection Z x (v 1))
  have hT : IsSmoothCovariantTensor T := by
    constructor
    · intro x
      let A : MultilinearMap ℝ (fun _ : Fin 2 => TangentSpace (𝓡 n) x) ℝ :=
        { toFun := T x
          map_update_add' := by
            intro _ v i a b
            fin_cases i <;> simp [T, map_add]
          map_update_smul' := by
            intro _ v i c a
            fin_cases i <;> simp [T, map_smul, smul_eq_mul] }
      exact ⟨A, fun _ => rfl⟩
    · intro U hU X hX
      have hcV := D.smooth.contMDiff.contMDiff
        (show ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          (∞ + 1) (T% V) Set.univ from by simpa using hV.contMDiffOn)
      have hcZ := D.smooth.contMDiff.contMDiff
        (show ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          (∞ + 1) (T% Z) Set.univ from by simpa using hZ.contMDiffOn)
      have hVX := (contMDiffOn_univ.mp hcV).contMDiffOn.clm_bundle_apply (hX 0)
      have hZX := (contMDiffOn_univ.mp hcZ).contMDiffOn.clm_bundle_apply (hX 1)
      have hi := (g.contMDiff.contMDiffOn.clm_bundle_apply hVX).clm_bundle_apply hZX
      intro x hx
      exact (Bundle.contMDiffAt_totalSpace.mp
        ((hi x hx).contMDiffAt (hU.mem_nhds hx))).2.contMDiffWithinAt
  have htrace := hT.tensorTrace (g := g) (k := 0)
  have h := htrace.2 Set.univ isOpen_univ (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  simpa only [contMDiffOn_univ, RiemannianMetric.tensorTrace, T,
    Fin.cons_zero, Fin.cons_one] using h

theorem connection_eq_zero_of_notMem_tsupport (D : LeviCivitaData g)
    {Z : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Z) x) (hx : x ∉ tsupport Z) : D.connection Z x = 0 := by
  have h := D.connection.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hZ
    (mdifferentiableAt_zeroSection ..) (by simp)
    (notMem_tsupport_iff_eventuallyEq.mp hx)
  exact h.trans (D.connection.isCovariantDerivativeOnUniv.zero (x := x))

theorem hasCompactSupport_inner_connection [R1Space M] (D : LeviCivitaData g)
    (V : (x : M) → TangentSpace (𝓡 n) x)
    {Z : (x : M) → TangentSpace (𝓡 n) x}
    (hZ : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z))
    (hc : HasCompactSupport Z) :
    HasCompactSupport (fun x => ∑ i,
      g.inner x (D.connection V x (g.orthonormalBasis x i))
        (D.connection Z x (g.orthonormalBasis x i))) := by
  apply HasCompactSupport.of_support_subset_isCompact hc
  intro x hx
  by_contra hx'
  exact hx (by simp [D.connection_eq_zero_of_notMem_tsupport
    ((hZ x).mdifferentiableAt (by simp)) hx'])

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]

theorem integrable_inner_connection (D : LeviCivitaData g)
    {V Z : (x : M) → TangentSpace (𝓡 n) x}
    (hV : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% V))
    (hZ : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z))
    (hc : HasCompactSupport Z) :
    Integrable (fun x => ∑ i,
      g.inner x (D.connection V x (g.orthonormalBasis x i))
        (D.connection Z x (g.orthonormalBasis x i))) g.volumeMeasure :=
  (D.contMDiff_inner_connection hV hZ).continuous.integrable_of_hasCompactSupport
    (D.hasCompactSupport_inner_connection V hZ hc)

end PoincareConjecture.LeviCivitaData
