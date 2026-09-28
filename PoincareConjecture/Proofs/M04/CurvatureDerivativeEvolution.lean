import PoincareConjecture.Proofs.M04.TensorTimeCommutator
import PoincareConjecture.Proofs.M04.TensorLaplacianCommutator
import PoincareConjecture.Proofs.M04.FlowRiemannRegularity
import PoincareConjecture.Proofs.M04.RiemannEvolutionInterior

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {J : Set ℝ}

set_option backward.isDefEq.respectTransparency false in
private theorem mdifferentiableAt_timeDeriv {U : Set M} {f : ℝ × M → ℝ}
    (hU : IsOpen U)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ f (J ×ˢ U))
    {t : ℝ} (ht : t ∈ interior J) {x : M} (hx : x ∈ U) :
    MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y ↦ deriv (fun s ↦ f (s, y)) t) x := by
  have htx : J ×ˢ U ∈ 𝓝 (t, x) :=
    prod_mem_nhds_iff.mpr ⟨mem_interior_iff_mem_nhds.mp ht, hU.mem_nhds hx⟩
  have hswap : ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun p : M × ℝ ↦ (p.2, p.1)) (x, t) :=
    contMDiffAt_snd.prodMk contMDiffAt_fst
  have hfs : ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ ↦ f (p.2, p.1)) (x, t) :=
    (hf.contMDiffAt htx).comp (x, t) hswap
  have hg : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) 1 (fun _ : M ↦ t) x :=
    contMDiffAt_const
  have hd := hfs.mfderiv (fun y s ↦ f (s, y)) (fun _ : M ↦ t) hg
    (by simpa only [Nat.cast_add, Nat.cast_one] using
      ENat.natCast_le_of_coe_top_le_withTop (N := (∞ : ℕ∞ω)) le_rfl (1 + 1))
  have he := hd.clm_apply
    (show ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) 1 (fun _ : M ↦ (1 : ℝ)) x from
      contMDiffAt_const)
  have hs : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) 1
      (fun y ↦ deriv (fun s ↦ f (s, y)) t) x := by
    simpa only [inTangentCoordinates_model_space, mfderiv_eq_fderiv, deriv] using he
  exact hs.mdifferentiableAt (by simp)

set_option backward.isDefEq.respectTransparency false in
private theorem covariantTensorDerivative_sub_at (D : LeviCivitaData g)
    {k : ℕ} (S T : CovariantTensorEvaluation n M k)
    (x : M) (a : TangentSpace (𝓡 n) x)
    (v : Fin k → TangentSpace (𝓡 n) x)
    (hS : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y ↦ S y (fun i ↦ FiberBundle.extend
        (EuclideanSpace ℝ (Fin n)) (v i) y)) x)
    (hT : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y ↦ T y (fun i ↦ FiberBundle.extend
        (EuclideanSpace ℝ (Fin n)) (v i) y)) x) :
    D.covariantTensorDerivative (fun y w ↦ S y w - T y w) x (Fin.cons a v) =
      D.covariantTensorDerivative S x (Fin.cons a v) -
        D.covariantTensorDerivative T x (Fin.cons a v) := by
  simp only [LeviCivitaData.covariantTensorDerivative, Fin.cons_zero, Fin.cons_succ,
    mvfderiv_fun_sub hS hT, sub_apply, Finset.sum_sub_distrib]
  ring

noncomputable def tensorHeatCorrection (D : LeviCivitaData g) {k : ℕ}
    (T : CovariantTensorEvaluation n M k) : CovariantTensorEvaluation n M (k + 1) :=
  fun x V ↦
    let a := V 0
    let v := fun i : Fin k ↦ V i.succ
    let b := g.orthonormalBasis x
    let K := D.covariantTensorDerivative T
    (∑ i, ∑ q, ((D.covariantTensorDerivative D.ricciEvaluation x ![a, v i, b q] +
      D.covariantTensorDerivative D.ricciEvaluation x ![v i, a, b q] -
      D.covariantTensorDerivative D.ricciEvaluation x ![b q, a, v i]) *
        T x (Function.update v i (b q)))) -
    (∑ p, ∑ q, (D.curvatureTensor x a (b p) (b q) (b p) *
      K x (Fin.cons (b q) v))) -
    2 * (∑ p, ∑ i, ∑ q, (D.curvatureTensor x a (b p) (b q) (v i) *
      K x (Fin.cons (b p) (Function.update v i (b q))))) -
    (∑ p, ∑ i, ∑ q, (D.covariantTensorDerivative D.riemannEvaluation x
      ![b p, a, b p, b q, v i] * T x (Function.update v i (b q))))

noncomputable def curvatureDerivativeReaction (D : LeviCivitaData g) :
    (m : ℕ) → CovariantTensorEvaluation n M (4 + m)
  | 0 => fun x v ↦ D.curvatureReaction x (v 0) (v 1) (v 2) (v 3)
  | m + 1 => fun x v ↦
      D.covariantTensorDerivative (curvatureDerivativeReaction D m) x v +
        tensorHeatCorrection D
          (D.iteratedCovariantTensorDerivative D.riemannEvaluation m) x v

set_option maxHeartbeats 2000000 in

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_iteratedRiemann_evolution (F : RicciFlow n M J)
    (m : ℕ) {t : ℝ} (ht : t ∈ interior J) (x : M)
    (v : Fin (4 + m) → TangentSpace (𝓡 n) x) :
    let D := F.connection t
    HasDerivAt
      (fun s ↦ (F.connection s).iteratedCovariantTensorDerivative
        (F.connection s).riemannEvaluation m x v)
      (D.tensorLaplacian (D.iteratedCovariantTensorDerivative
        D.riemannEvaluation m) x v + curvatureDerivativeReaction D m x v) t := by
  classical
  let D := F.connection t
  let U (j : ℕ) (s : ℝ) := (F.connection s).iteratedCovariantTensorDerivative
    (F.connection s).riemannEvaluation j
  have hSmooth (j : ℕ) (s : ℝ) : IsSmoothCovariantTensor (U j s) := by
    induction j with
    | zero => exact isSmoothCovariantTensor_riemannEvaluation (F.connection s)
    | succ j ih => exact isSmoothCovariantTensor_covariantTensorDerivative (F.connection s) ih
  have hJoint (j : ℕ) (V : Set M) (hV : IsOpen V)
      (X : Fin (4 + j) → (y : M) → TangentSpace (𝓡 n) y)
      (hX : ∀ i, ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (X i)) V) :
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M ↦ U j p.1 p.2 (fun i ↦ X i p.2)) (J ×ˢ V) :=
    contMDiffOn_flow_iteratedCovariantTensorDerivative F
      (fun s ↦ isSmoothCovariantTensor_riemannEvaluation (F.connection s))
      (fun W hW Y hY ↦ contMDiffOn_flow_riemannEvaluation F hW Y hY) j hV hX
  induction m generalizing x with
  | zero =>
    have hv : ![v 0, v 1, v 2, v 3] = v := by
      funext i
      fin_cases i <;> rfl
    simpa only [LeviCivitaData.iteratedCovariantTensorDerivative,
      LeviCivitaData.riemannEvaluation, curvatureDerivativeReaction, hv] using
      hasDerivAt_curvatureTensor_evolution F ht x (v 0) (v 1) (v 2) (v 3)
  | succ m ih =>
    let a := v 0
    let w : Fin (4 + m) → TangentSpace (𝓡 n) x := fun i ↦ v i.succ
    have hv : Fin.cons a w = v := by
      funext i
      cases i using Fin.cases <;> rfl
    rw [← hv]
    let S : CovariantTensorEvaluation n M (4 + m) :=
      fun y z ↦ deriv (fun s ↦ U m s y z) t
    let L := D.tensorLaplacian (U m t)
    have hQ : curvatureDerivativeReaction D m = (fun y z ↦ S y z - L y z) := by
      funext y z
      have he : S y z = L y z + curvatureDerivativeReaction D m y z :=
        (ih y z).deriv
      linarith only [he]
    let e := trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
    let W := fun i ↦ FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (w i)
    have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
    have hW (i : Fin (4 + m)) : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (W i)) e.baseSet :=
      contMDiffOn_extend_baseSet (w i)
    have hS : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
        (fun y ↦ S y (fun i ↦ W i y)) x :=
      mdifferentiableAt_timeDeriv e.open_baseSet
        (hJoint m e.baseSet e.open_baseSet W hW) ht hx
    have hL : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
        (fun y ↦ L y (fun i ↦ W i y)) x :=
      (((isSmoothCovariantTensor_tensorLaplacian D (hSmooth m t)).2
        e.baseSet e.open_baseSet W hW).contMDiffAt
          (e.open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
    have hsub := covariantTensorDerivative_sub_at D S L x a w hS hL
    rw [← hQ] at hsub
    have hspace := covariantTensorDerivative_tensorLaplacian_commutator D
      (hSmooth m t) x a w
    dsimp only at hspace
    change D.covariantTensorDerivative L x (Fin.cons a w) -
      D.tensorLaplacian (U (m + 1) t) x (Fin.cons a w) = _ at hspace
    have htime := hasDerivAt_covariantTensorDerivative F (hSmooth m)
      (hJoint m) ht x a w
    apply htime.congr_deriv
    rw [curvatureDerivativeReaction]
    simp only [tensorHeatCorrection, Fin.cons_zero, Fin.cons_succ]
    dsimp only [D, U, S, L] at hsub hspace ⊢
    linarith only [hsub, hspace]

end PoincareConjecture.M04
