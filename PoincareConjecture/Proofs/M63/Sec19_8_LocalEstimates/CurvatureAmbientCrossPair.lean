import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.CurveTensorLeibniz
import PoincareConjecture.Proofs.M04.ScalarContractions

set_option autoImplicit false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem m63CurvatureAmbientPair_jet_derivative [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) (j : ℕ)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ) :
    let D := F.connection t
    let R := D.riemannEvaluation
    let T := D.covariantTensorDerivative D.ricciEvaluation
    let U := D.covariantTensorDerivative T
    let J := D.covariantTensorDerivative R
    let S := spatialUnitTangent F c t
    let H := m63CurvatureJet F c 0 t
    let B := m63CurvatureJet F c 1 t
    let Z := m63CurvatureJet F c j t
    let W := m63CurvatureJet F c (j + 1) t
    let E := fun y => R (c y t) ![H y, S y, Z y, S y] -
      2 * T (c y t) ![S y, S y, Z y] + T (c y t) ![Z y, S y, S y]
    DifferentiableAt ℝ E x ∧
      m62ArcDerivative F c t E x =
        (R (c x t) ![H x, S x, W x, S x] -
          2 * T (c x t) ![S x, S x, W x] + T (c x t) ![W x, S x, S x]) +
        (J (c x t) ![S x, H x, S x, Z x, S x] +
          R (c x t) ![B x, S x, Z x, S x] + R (c x t) ![H x, S x, Z x, H x] -
          2 * U (c x t) ![S x, S x, S x, Z x] + U (c x t) ![S x, Z x, S x, S x] -
          2 * T (c x t) ![H x, S x, Z x] - 2 * T (c x t) ![S x, H x, Z x] +
          2 * T (c x t) ![Z x, S x, H x]) := by
  let D := F.connection t
  let R := D.riemannEvaluation
  let T := D.covariantTensorDerivative D.ricciEvaluation
  let U := D.covariantTensorDerivative T
  let J := D.covariantTensorDerivative R
  let S : (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2) :=
    fun z => spatialUnitTangent F c z.2 z.1
  let H : (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2) :=
    fun z => m63CurvatureJet F c 0 z.2 z.1
  let B : (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2) :=
    fun z => m63CurvatureJet F c 1 z.2 z.1
  let Z : (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2) :=
    fun z => m63CurvatureJet F c j z.2 z.1
  let W : (y : ℝ) → TangentSpace (𝓡 n) (c y t) := m63CurvatureJet F c (j + 1) t
  let YR : Fin 4 → (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2) := ![H, S, Z, S]
  let YT : Fin 3 → (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2) := ![S, S, Z]
  let YT' : Fin 3 → (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2) := ![Z, S, S]
  let fR : ℝ → ℝ := fun y => R (c y t) ![H (y, t), S (y, t), Z (y, t), S (y, t)]
  let fT : ℝ → ℝ := fun y => T (c y t) ![S (y, t), S (y, t), Z (y, t)]
  let fT' : ℝ → ℝ := fun y => T (c y t) ![Z (y, t), S (y, t), S (y, t)]
  have hReval (z : ℝ × ℝ) : (fun i => YR i z) = ![H z, S z, Z z, S z] := by
    funext i
    fin_cases i <;> rfl
  have hTeval (z : ℝ × ℝ) : (fun i => YT i z) = ![S z, S z, Z z] := by
    funext i
    fin_cases i <;> rfl
  have hTeval' (z : ℝ × ℝ) : (fun i => YT' i z) = ![Z z, S z, S z] := by
    funext i
    fin_cases i <;> rfl
  change DifferentiableAt ℝ (fun y => fR y - 2 * fT y + fT' y) x ∧
    m62ArcDerivative F c t (fun y => fR y - 2 * fT y + fT' y) x =
      (R (c x t) ![H (x, t), S (x, t), W x, S (x, t)] -
        2 * T (c x t) ![S (x, t), S (x, t), W x] +
        T (c x t) ![W x, S (x, t), S (x, t)]) +
      (J (c x t) ![S (x, t), H (x, t), S (x, t), Z (x, t), S (x, t)] +
        R (c x t) ![B (x, t), S (x, t), Z (x, t), S (x, t)] +
        R (c x t) ![H (x, t), S (x, t), Z (x, t), H (x, t)] -
        2 * U (c x t) ![S (x, t), S (x, t), S (x, t), Z (x, t)] +
        U (c x t) ![S (x, t), Z (x, t), S (x, t), S (x, t)] -
        2 * T (c x t) ![H (x, t), S (x, t), Z (x, t)] -
        2 * T (c x t) ![S (x, t), H (x, t), Z (x, t)] +
        2 * T (c x t) ![Z (x, t), S (x, t), H (x, t)])
  have hS := unitTangent_joint_contMDiff F c hc
  have hH := M63.curvatureJet_joint_contMDiff F c hc 0
  have hZ := M63.curvatureJet_joint_contMDiff F c hc j
  have hYR (i : Fin 4) : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z => (⟨c z.1 z.2, YR i z⟩ : TangentBundle (𝓡 n) M))
      (univ ×ˢ Ioo a b) := by
    fin_cases i
    · exact hH
    · exact hS
    · exact hZ
    · exact hS
  have hYT (i : Fin 3) : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z => (⟨c z.1 z.2, YT i z⟩ : TangentBundle (𝓡 n) M))
      (univ ×ˢ Ioo a b) := by
    fin_cases i
    · exact hS
    · exact hS
    · exact hZ
  have hYT' (i : Fin 3) : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z => (⟨c z.1 z.2, YT' i z⟩ : TangentBundle (𝓡 n) M))
      (univ ×ˢ Ioo a b) := by
    fin_cases i
    · exact hZ
    · exact hS
    · exact hS
  have hR := M04.isSmoothCovariantTensor_riemannEvaluation D
  have hT := M04.isSmoothCovariantTensor_covariantTensorDerivative D
    (M04.isSmoothCovariantTensor_ricciEvaluation D)
  have hopen : IsOpen (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := isOpen_univ.prod isOpen_Ioo
  have hmem : (x, t) ∈ (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := ⟨mem_univ _, ht⟩
  have hs : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun y : ℝ => (y, t)) x :=
    (contDiffAt_id.prodMk contDiffAt_const).contMDiffAt
  have hcurve : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun y => c y t) x :=
    (hc.joint_smooth.contMDiffAt (hopen.mem_nhds hmem)).comp x hs
  have hRs : DifferentiableAt ℝ fR x := by
    have h := (m63HasDerivAt_tensor_pullback D R hR hcurve (fun i y => YR i (y, t))
      (fun i => (((hYR i).contMDiffAt (hopen.mem_nhds hmem)).comp x hs).mdifferentiableAt
        (by simp))).differentiableAt
    simpa only [hReval] using h
  have hTs : DifferentiableAt ℝ fT x := by
    have h := (m63HasDerivAt_tensor_pullback D T hT hcurve (fun i y => YT i (y, t))
      (fun i => (((hYT i).contMDiffAt (hopen.mem_nhds hmem)).comp x hs).mdifferentiableAt
        (by simp))).differentiableAt
    simpa only [hTeval] using h
  have hTs' : DifferentiableAt ℝ fT' x := by
    have h := (m63HasDerivAt_tensor_pullback D T hT hcurve (fun i y => YT' i (y, t))
      (fun i => (((hYT' i).contMDiffAt (hopen.mem_nhds hmem)).comp x hs).mdifferentiableAt
        (by simp))).differentiableAt
    simpa only [hTeval'] using h
  refine ⟨hRs.sub (hTs.const_mul 2) |>.add hTs', ?_⟩
  have hRarc := m63ArcDerivative_tensor_pullback F c hc R hR YR hYR ht x
  have hTarc := m63ArcDerivative_tensor_pullback F c hc T hT YT hYT ht x
  have hTarc' := m63ArcDerivative_tensor_pullback F c hc T hT YT' hYT' ht x
  have hRslot (i : Fin 4) :
      R (c x t) (Function.update (fun l => YR l (x, t)) i
        (m62SpatialDerivative F c t (fun y => YR i (y, t)) x)) =
      (![R (c x t) ![B (x, t), S (x, t), Z (x, t), S (x, t)],
        R (c x t) ![H (x, t), H (x, t), Z (x, t), S (x, t)],
        R (c x t) ![H (x, t), S (x, t), W x, S (x, t)],
        R (c x t) ![H (x, t), S (x, t), Z (x, t), H (x, t)]] : Fin 4 → ℝ) i := by
    fin_cases i <;> apply congrArg (R (c x t)) <;> funext l <;> fin_cases l <;> rfl
  have hTslot (i : Fin 3) :
      T (c x t) (Function.update (fun l => YT l (x, t)) i
        (m62SpatialDerivative F c t (fun y => YT i (y, t)) x)) =
      (![T (c x t) ![H (x, t), S (x, t), Z (x, t)],
        T (c x t) ![S (x, t), H (x, t), Z (x, t)],
        T (c x t) ![S (x, t), S (x, t), W x]] : Fin 3 → ℝ) i := by
    fin_cases i <;> apply congrArg (T (c x t)) <;> funext l <;> fin_cases l <;> rfl
  have hTslot' (i : Fin 3) :
      T (c x t) (Function.update (fun l => YT' l (x, t)) i
        (m62SpatialDerivative F c t (fun y => YT' i (y, t)) x)) =
      (![T (c x t) ![W x, S (x, t), S (x, t)],
        T (c x t) ![Z (x, t), H (x, t), S (x, t)],
        T (c x t) ![Z (x, t), S (x, t), H (x, t)]] : Fin 3 → ℝ) i := by
    fin_cases i <;> apply congrArg (T (c x t)) <;> funext l <;> fin_cases l <;> rfl
  simp_rw [hRslot] at hRarc
  simp_rw [hTslot] at hTarc
  simp_rw [hTslot'] at hTarc'
  simp only [hReval] at hRarc
  simp only [hTeval] at hTarc
  simp only [hTeval'] at hTarc'
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, add_zero] at hRarc hTarc hTarc'
  change m62ArcDerivative F c t fR x =
    J (c x t) ![S (x, t), H (x, t), S (x, t), Z (x, t), S (x, t)] +
      (R (c x t) ![B (x, t), S (x, t), Z (x, t), S (x, t)] +
        (R (c x t) ![H (x, t), H (x, t), Z (x, t), S (x, t)] +
          (R (c x t) ![H (x, t), S (x, t), W x, S (x, t)] +
            R (c x t) ![H (x, t), S (x, t), Z (x, t), H (x, t)]))) at hRarc
  change m62ArcDerivative F c t fT x =
    U (c x t) ![S (x, t), S (x, t), S (x, t), Z (x, t)] +
      (T (c x t) ![H (x, t), S (x, t), Z (x, t)] +
        (T (c x t) ![S (x, t), H (x, t), Z (x, t)] +
          T (c x t) ![S (x, t), S (x, t), W x])) at hTarc
  change m62ArcDerivative F c t fT' x =
    U (c x t) ![S (x, t), Z (x, t), S (x, t), S (x, t)] +
      (T (c x t) ![W x, S (x, t), S (x, t)] +
        (T (c x t) ![Z (x, t), H (x, t), S (x, t)] +
          T (c x t) ![Z (x, t), S (x, t), H (x, t)])) at hTarc'
  have hzero : R (c x t) ![H (x, t), H (x, t), Z (x, t), S (x, t)] = 0 := by
    change D.curvatureTensor (c x t) (H (x, t)) (H (x, t)) (Z (x, t)) (S (x, t)) = 0
    rw [LeviCivitaData.curvatureTensor, M04.curvature_self, map_zero]
    rfl
  have hsym : T (c x t) ![Z (x, t), H (x, t), S (x, t)] =
      T (c x t) ![Z (x, t), S (x, t), H (x, t)] :=
    M04.ricci_covariantDerivative_symm D (c x t) _ _ _
  have hcombine : m62ArcDerivative F c t (fun y => fR y - 2 * fT y + fT' y) x =
      m62ArcDerivative F c t fR x - 2 * m62ArcDerivative F c t fT x +
        m62ArcDerivative F c t fT' x := by
    have hd : HasDerivAt (fun y => fR y - 2 * fT y + fT' y)
        (deriv fR x - 2 * deriv fT x + deriv fT' x) x :=
      (hRs.hasDerivAt.sub (hTs.hasDerivAt.const_mul 2)).add hTs'.hasDerivAt
    rw [m62ArcDerivative, hd.deriv]
    dsimp only [m62ArcDerivative]
    ring
  rw [hcombine, hRarc, hTarc, hTarc', hzero, hsym]
  ring

end PoincareConjecture
