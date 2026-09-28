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




theorem m63TangentRicci_arc_derivatives [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ) :
    let D := F.connection t
    let T := D.covariantTensorDerivative D.ricciEvaluation
    let U := D.covariantTensorDerivative T
    let S := spatialUnitTangent F c t x
    let H := m63CurvatureJet F c 0 t x
    let B := m63CurvatureJet F c 1 t x
    m62ArcDerivative F c t (m62TangentRicci F c t) x =
        T (c x t) ![S, S, S] + 2 * D.ricci (c x t) H S ∧
      m62ArcSecondDerivative F c t (m62TangentRicci F c t) x =
        U (c x t) ![S, S, S, S] + T (c x t) ![H, S, S] +
          4 * T (c x t) ![S, H, S] + 2 * D.ricci (c x t) B S +
          2 * D.ricci (c x t) H H := by
  let D := F.connection t
  let T := D.covariantTensorDerivative D.ricciEvaluation
  let U := D.covariantTensorDerivative T
  let S : (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2) :=
    fun z => spatialUnitTangent F c z.2 z.1
  let H : (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2) :=
    fun z => m63CurvatureJet F c 0 z.2 z.1
  let B := m63CurvatureJet F c 1 t x
  let YS : Fin 2 → (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2) := ![S, S]
  let YT : Fin 3 → (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2) := ![S, S, S]
  let YH : Fin 2 → (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2) := ![H, S]
  have hS := unitTangent_joint_contMDiff F c hc
  have hH := M63.curvatureJet_joint_contMDiff F c hc 0
  have hYS (i : Fin 2) : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z => (⟨c z.1 z.2, YS i z⟩ : TangentBundle (𝓡 n) M))
      (univ ×ˢ Ioo a b) := by
    fin_cases i <;> exact hS
  have hYT (i : Fin 3) : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z => (⟨c z.1 z.2, YT i z⟩ : TangentBundle (𝓡 n) M))
      (univ ×ˢ Ioo a b) := by
    fin_cases i <;> exact hS
  have hYH (i : Fin 2) : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z => (⟨c z.1 z.2, YH i z⟩ : TangentBundle (𝓡 n) M))
      (univ ×ˢ Ioo a b) := by
    fin_cases i
    · exact hH
    · exact hS
  have hSval (z : ℝ × ℝ) : (fun i => YS i z) = ![S z, S z] := by
    funext i
    fin_cases i <;> rfl
  have hTval (z : ℝ × ℝ) : (fun i => YT i z) = ![S z, S z, S z] := by
    funext i
    fin_cases i <;> rfl
  have hHval (z : ℝ × ℝ) : (fun i => YH i z) = ![H z, S z] := by
    funext i
    fin_cases i <;> rfl
  have hRic := M04.isSmoothCovariantTensor_ricciEvaluation D
  have hT := M04.isSmoothCovariantTensor_covariantTensorDerivative D hRic
  have hfirst (y : ℝ) : m62ArcDerivative F c t (m62TangentRicci F c t) y =
      T (c y t) ![S (y, t), S (y, t), S (y, t)] +
        2 * D.ricci (c y t) (H (y, t)) (S (y, t)) := by
    have h := m63ArcDerivative_tensor_pullback F c hc D.ricciEvaluation hRic YS hYS ht y
    have hslot (i : Fin 2) :
        D.ricciEvaluation (c y t) (Function.update (fun j => YS j (y, t)) i
          (m62SpatialDerivative F c t (fun z => YS i (z, t)) y)) =
        (![D.ricciEvaluation (c y t) ![H (y, t), S (y, t)],
          D.ricciEvaluation (c y t) ![S (y, t), H (y, t)]] : Fin 2 → ℝ) i := by
      fin_cases i <;> apply congrArg (D.ricciEvaluation (c y t)) <;>
        funext j <;> fin_cases j <;> rfl
    simp_rw [hslot] at h
    simp only [hSval, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, add_zero] at h
    change m62ArcDerivative F c t (m62TangentRicci F c t) y =
      T (c y t) ![S (y, t), S (y, t), S (y, t)] +
        (D.ricci (c y t) (H (y, t)) (S (y, t)) +
          D.ricci (c y t) (S (y, t)) (H (y, t))) at h
    rw [M04.ricci_symm D (c y t) (S (y, t)) (H (y, t))] at h
    linarith only [h]
  refine ⟨hfirst x, ?_⟩
  let fT : ℝ → ℝ := fun y => T (c y t) ![S (y, t), S (y, t), S (y, t)]
  let fR : ℝ → ℝ := fun y => D.ricciEvaluation (c y t) ![H (y, t), S (y, t)]
  have hopen : IsOpen (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := isOpen_univ.prod isOpen_Ioo
  have hmem : (x, t) ∈ (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := ⟨mem_univ _, ht⟩
  have hs : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun y : ℝ => (y, t)) x :=
    (contDiffAt_id.prodMk contDiffAt_const).contMDiffAt
  have hcurve : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun y => c y t) x :=
    (hc.joint_smooth.contMDiffAt (hopen.mem_nhds hmem)).comp x hs
  have hTs : DifferentiableAt ℝ fT x := by
    have h := (m63HasDerivAt_tensor_pullback D T hT hcurve (fun i y => YT i (y, t))
      (fun i => (((hYT i).contMDiffAt (hopen.mem_nhds hmem)).comp x hs).mdifferentiableAt
        (by simp))).differentiableAt
    simpa only [hTval] using h
  have hRs : DifferentiableAt ℝ fR x := by
    have h := (m63HasDerivAt_tensor_pullback D D.ricciEvaluation hRic hcurve
      (fun i y => YH i (y, t))
      (fun i => (((hYH i).contMDiffAt (hopen.mem_nhds hmem)).comp x hs).mdifferentiableAt
        (by simp))).differentiableAt
    simpa only [hHval] using h
  have hTarc := m63ArcDerivative_tensor_pullback F c hc T hT YT hYT ht x
  have hRarc := m63ArcDerivative_tensor_pullback F c hc D.ricciEvaluation hRic YH hYH ht x
  have hTslot (i : Fin 3) :
      T (c x t) (Function.update (fun j => YT j (x, t)) i
        (m62SpatialDerivative F c t (fun y => YT i (y, t)) x)) =
      (![T (c x t) ![H (x, t), S (x, t), S (x, t)],
        T (c x t) ![S (x, t), H (x, t), S (x, t)],
        T (c x t) ![S (x, t), S (x, t), H (x, t)]] : Fin 3 → ℝ) i := by
    fin_cases i <;> apply congrArg (T (c x t)) <;> funext j <;> fin_cases j <;> rfl
  have hRslot (i : Fin 2) :
      D.ricciEvaluation (c x t) (Function.update (fun j => YH j (x, t)) i
        (m62SpatialDerivative F c t (fun y => YH i (y, t)) x)) =
      (![D.ricciEvaluation (c x t) ![B, S (x, t)],
        D.ricciEvaluation (c x t) ![H (x, t), H (x, t)]] : Fin 2 → ℝ) i := by
    fin_cases i <;> apply congrArg (D.ricciEvaluation (c x t)) <;>
      funext j <;> fin_cases j <;> rfl
  simp_rw [hTslot] at hTarc
  simp_rw [hRslot] at hRarc
  simp only [hTval, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, add_zero] at hTarc
  simp only [hHval, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, add_zero] at hRarc
  change m62ArcDerivative F c t fT x =
    U (c x t) ![S (x, t), S (x, t), S (x, t), S (x, t)] +
      (T (c x t) ![H (x, t), S (x, t), S (x, t)] +
        (T (c x t) ![S (x, t), H (x, t), S (x, t)] +
          T (c x t) ![S (x, t), S (x, t), H (x, t)])) at hTarc
  change m62ArcDerivative F c t fR x =
    T (c x t) ![S (x, t), H (x, t), S (x, t)] +
      (D.ricci (c x t) B (S (x, t)) + D.ricci (c x t) (H (x, t)) (H (x, t))) at hRarc
  have hsym : T (c x t) ![S (x, t), S (x, t), H (x, t)] =
      T (c x t) ![S (x, t), H (x, t), S (x, t)] :=
    M04.ricci_covariantDerivative_symm D (c x t) _ _ _
  have hcombine : m62ArcDerivative F c t (fun y => fT y + 2 * fR y) x =
      m62ArcDerivative F c t fT x + 2 * m62ArcDerivative F c t fR x := by
    have hd : HasDerivAt (fun y => fT y + 2 * fR y)
        (deriv fT x + 2 * deriv fR x) x := hTs.hasDerivAt.add (hRs.hasDerivAt.const_mul 2)
    rw [m62ArcDerivative, hd.deriv]
    dsimp only [m62ArcDerivative]
    ring
  change m62ArcDerivative F c t (fun y => m62ArcDerivative F c t (m62TangentRicci F c t) y) x =
    U (c x t) ![S (x, t), S (x, t), S (x, t), S (x, t)] +
      T (c x t) ![H (x, t), S (x, t), S (x, t)] +
      4 * T (c x t) ![S (x, t), H (x, t), S (x, t)] +
      2 * D.ricci (c x t) B (S (x, t)) + 2 * D.ricci (c x t) (H (x, t)) (H (x, t))
  rw [show (fun y => m62ArcDerivative F c t (m62TangentRicci F c t) y) =
      (fun y => fT y + 2 * fR y) from funext hfirst, hcombine, hTarc, hRarc, hsym]
  ring

end PoincareConjecture
