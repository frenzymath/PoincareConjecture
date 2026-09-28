import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Evolution.Tensor.FlowTensorRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Evolution.Scalar.SpatialCoefficients
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Identities.RicciCommutator
import Mathlib.LinearAlgebra.Multilinear.Curry

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter Function

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {U : Set M}

set_option maxHeartbeats 1600000 in

set_option backward.isDefEq.respectTransparency false in
theorem continuousOn_flow_ricciEvolutionRHS_onFields (F : RicciFlow n M J)
    (hU : IsOpen U) {X Y : (y : M) → TangentSpace (𝓡 n) y}
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U) :
    ContinuousOn
      (fun p : ℝ × M ↦
        (F.connection p.1).tensorLaplacian (F.connection p.1).ricciEvaluation
          p.2 ![X p.2, Y p.2] +
        (F.connection p.1).ricciReaction p.2 (X p.2) (Y p.2)) (J ×ˢ U) := by
  classical
  let H : ℝ → CovariantTensorEvaluation n M 4 := fun s ↦
    (F.connection s).iteratedCovariantTensorDerivative (F.connection s).ricciEvaluation 2
  have hH (s : ℝ) : IsSmoothCovariantTensor (H s) :=
    isSmoothCovariantTensor_covariantTensorDerivative (F.connection s)
      (isSmoothCovariantTensor_covariantTensorDerivative (F.connection s)
        (isSmoothCovariantTensor_ricciEvaluation (F.connection s)))
  have hjoint {V : Set M} (hV : IsOpen V)
      (Z : Fin 4 → (y : M) → TangentSpace (𝓡 n) y)
      (hZ : ∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ∞ (T% (Z i)) V) :
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M ↦ H p.1 p.2 (fun i ↦ Z i p.2)) (J ×ˢ V) :=
    contMDiffOn_flow_iteratedCovariantTensorDerivative F
      (fun s ↦ isSmoothCovariantTensor_ricciEvaluation (F.connection s))
      (fun W hW Z hZ ↦ contMDiffOn_flow_ricciEvaluation F hW hZ) 2 hV hZ
  have hfour {V : Set M} (hV : IsOpen V)
      (A B C D : (y : M) → TangentSpace (𝓡 n) y)
      (hA : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) V)
      (hB : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) V)
      (hC : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% C) V)
      (hD : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% D) V) :
      ContinuousOn (fun p : ℝ × M ↦ H p.1 p.2 ![A p.2, B p.2, C p.2, D p.2])
        (J ×ˢ V) := by
    have hZ : ∀ i : Fin 4,
        ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          ∞ (T% (![A, B, C, D] i)) V := by
      intro i
      fin_cases i
      · exact hA
      · exact hB
      · exact hC
      · exact hD
    apply (hjoint hV ![A, B, C, D] hZ).continuousOn.congr
    intro p hp
    apply congrArg (H p.1 p.2)
    funext i
    fin_cases i <;> rfl
  choose A hA using fun p : ℝ × M ↦ (hH p.1).1 p.2
  let S : Fin 3 → (p : ℝ × M) →
      MultilinearMap ℝ (fun _ : Fin 2 ↦ TangentSpace (𝓡 n) p.2) ℝ :=
    fun i p ↦ (((A p).curryMid (Fin.last 3)) (Y p.2)).curryMid i (X p.2)
  have hS2 (p : ℝ × M) (r s : TangentSpace (𝓡 n) p.2) :
      S 2 p ![r, s] = H p.1 p.2 ![r, s, X p.2, Y p.2] := by
    calc
      _ = A p ![r, s, X p.2, Y p.2] := by
        apply congrArg (A p)
        funext i
        fin_cases i <;> rfl
      _ = _ := (hA p _).symm
  have hS0 (p : ℝ × M) (r s : TangentSpace (𝓡 n) p.2) :
      S 0 p ![r, s] = H p.1 p.2 ![X p.2, r, s, Y p.2] := by
    calc
      _ = A p ![X p.2, r, s, Y p.2] := by
        apply congrArg (A p)
        funext i
        fin_cases i <;> rfl
      _ = _ := (hA p _).symm
  have hS1 (p : ℝ × M) (r s : TangentSpace (𝓡 n) p.2) :
      S 1 p ![r, s] = H p.1 p.2 ![r, X p.2, s, Y p.2] := by
    calc
      _ = A p ![r, X p.2, s, Y p.2] := by
        apply congrArg (A p)
        funext i
        fin_cases i <;> rfl
      _ = _ := (hA p _).symm
  let D : Fin 3 → ℝ × M → ℝ := fun j p ↦ ∑ i, S j p
    ![(F.metric p.1).orthonormalBasis p.2 i, (F.metric p.1).orthonormalBasis p.2 i]
  have hD (j : Fin 3) : ContinuousOn (D j) (J ×ˢ U) := by
    apply continuousOn_flow_tensorTrace F hU (S j)
    intro V hV hVU R Q hR hQ
    fin_cases j
    · apply (hfour hV X R Q Y (hX.mono hVU) hR hQ (hY.mono hVU)).congr
      intro p hp
      exact hS0 p (R p.2) (Q p.2)
    · apply (hfour hV R X Q Y hR (hX.mono hVU) hQ (hY.mono hVU)).congr
      intro p hp
      exact hS1 p (R p.2) (Q p.2)
    · apply (hfour hV R Q X Y hR hQ (hX.mono hVU) (hY.mono hVU)).congr
      intro p hp
      exact hS2 p (R p.2) (Q p.2)
  have hlap (p : ℝ × M) :
      (F.connection p.1).tensorLaplacian (F.connection p.1).ricciEvaluation
        p.2 ![X p.2, Y p.2] = D 2 p := by
    simp only [LeviCivitaData.tensorLaplacian, D, hS2]
    apply Finset.sum_congr rfl
    intro i hi
    apply congrArg (H p.1 p.2)
    funext j
    fin_cases j <;> rfl
  have hreact (p : ℝ × M) :
      (F.connection p.1).ricciReaction p.2 (X p.2) (Y p.2) =
        2 * (D 0 p - D 1 p) := by
    simpa only [D, hS0, hS1, H, Finset.sum_sub_distrib] using
      (ricci_second_derivative_commutator_trace (F.connection p.1) p.2
        (X p.2) (Y p.2)).symm
  have hc : ContinuousOn (fun p ↦ D 2 p + 2 * (D 0 p - D 1 p)) (J ×ˢ U) :=
    (hD 2).add ((continuousOn_const (c := (2 : ℝ))).mul ((hD 0).sub (hD 1)))
  apply hc.congr
  intro p hp
  exact congrArg₂ (fun a b : ℝ ↦ a + b) (hlap p) (hreact p)

private theorem continuousOn_fixedFiberInputs {E : M → Type*}
    (G : ℝ → (y : M) → E y → E y → ℝ) (X Y : (y : M) → E y)
    (hG : ContinuousOn (fun p : ℝ × M ↦ G p.1 p.2 (X p.2) (Y p.2)) (J ×ˢ U))
    (x : M) (hx : x ∈ U) (u v : E x) (hXu : X x = u) (hYv : Y x = v) :
    ContinuousOn (fun s ↦ G s x u v) J := by
  have hslice : ContinuousOn (fun s ↦ G s x (X x) (Y x)) J :=
    hG.comp (continuous_id.prodMk continuous_const).continuousOn
      (show MapsTo (fun s : ℝ ↦ (s, x)) J (J ×ˢ U) from fun _ hs ↦ ⟨hs, hx⟩)
  simpa only [hXu, hYv] using hslice

set_option maxHeartbeats 1000000 in

theorem continuousOn_ricciEvolutionRHS_timeSlice (F : RicciFlow n M J)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    ContinuousOn
      (fun s : ℝ ↦
        (F.connection s).tensorLaplacian (F.connection s).ricciEvaluation x ![u, v] +
        (F.connection s).ricciReaction x u v) J := by
  let t := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _) x
  have hx : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u
  let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  have hXu : X x = u := FiberBundle.extend_apply_self _ _
  have hYv : Y x = v := FiberBundle.extend_apply_self _ _
  have hjoint := continuousOn_flow_ricciEvolutionRHS_onFields F t.open_baseSet (X := X) (Y := Y)
    (contMDiffOn_extend_baseSet u) (contMDiffOn_extend_baseSet v)
  exact continuousOn_fixedFiberInputs
    (fun s y a b ↦
      (F.connection s).tensorLaplacian (F.connection s).ricciEvaluation y ![a, b] +
        (F.connection s).ricciReaction y a b) X Y hjoint x hx u v hXu hYv

end PoincareConjecture.RicciFlowAnalysis
