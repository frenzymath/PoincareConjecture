import PoincareConjecture.Proofs.M09.SharpAdaptedIndex
import PoincareConjecture.Proofs.M09.TerminalAdaptedFrame
import PoincareConjecture.Proofs.M09.LocalHessianSymmetry
import Mathlib.Analysis.Normed.Module.Normalize

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace
open Filter NormedSpace

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T2Space M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option maxHeartbeats 2000000 in

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_tensor_eq_of_sharp_lower_contact
    (hM04 : RicciFlowCurvatureTheory.{u}) (hL : LGeodesicTheory F T τmax)
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (A : LExponentialFamily F T τmax p) (Z : TangentSpace (𝓡 n) p)
    (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (hmin : IsMinimizingBackwardLPath F T 0 b (A.path Z b hb hmax))
    (f : M → ℝ) (O : Set M) (hO : IsOpen O) (hqO : A.gamma Z b ∈ O)
    (hf : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f O)
    (hvalue : f (A.gamma Z b) = A.action Z b / (2 * Real.sqrt b))
    (hlower : ∀ᶠ q in 𝓝 (A.gamma Z b), f q ≤ reducedLength F T p q b)
    (hsharp : (F.connection (T - b)).laplacian f (A.gamma Z b) =
      (n : ℝ) / (2 * b) - (F.connection (T - b)).scalarCurvature (A.gamma Z b) -
        reducedHarnackIntegral F T (A.gamma Z)
          (backwardScalarEvolutionAlong F T (A.gamma Z)) b / (2 * b * Real.sqrt b)) :
    ∀ v w : TangentSpace (𝓡 n) (A.gamma Z b),
      (F.connection (T - b)).ricci (A.gamma Z b) v w +
        (F.connection (T - b)).hessian f (A.gamma Z b) v w =
          (F.metric (T - b)).inner (A.gamma Z b) v w / (2 * b) := by
  classical
  let c := Real.sqrt b
  let q := A.gamma Z b
  let g := F.metric (T - b)
  let D := F.connection (T - b)
  have hc : 0 < c := Real.sqrt_pos.mpr hb
  have hc2 : c ^ 2 = b := Real.sq_sqrt hb.le
  have hctime : c ∈ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax) :=
    ⟨(neg_lt_zero.mpr (Real.sqrt_pos.mpr hτmax)).trans hc,
      Real.sqrt_lt_sqrt hb.le hmax⟩
  have hend : A.squareFamily Z c = q :=
    (A.square_agrees Z c ⟨hc.le, hctime.2⟩).trans (congrArg (A.gamma Z) hc2)
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let R := tensorBilinear g D.ricciEvaluation (hM04.tensor_calculus n M g D).2.1 q
  have hR (v w : TangentSpace (𝓡 n) q) : R v w = D.ricci q v w :=
    tensorBilinear_apply g D.ricciEvaluation (hM04.tensor_calculus n M g D).2.1 q v w
  obtain ⟨H, hH⟩ := squareTime_hessian_exists_bilinear_local F T τmax hτmax hwindow
    q c hctime f O hO hqO hf
  rw [hc2] at hH
  have hunit (u : TangentSpace (𝓡 n) q) (hu : g.inner q u u = 1) :
      R u u + H u u = 1 / (2 * b) := by
    obtain ⟨e, i, hei, he⟩ := exists_orthonormal_vectors_containing_unit g q u hu
    have he' : ∀ j k, (F.metric (T - c ^ 2)).inner (A.squareFamily Z c) (e j) (e k) =
        if j = k then 1 else 0 := by
      rw [hc2, hend]
      exact he
    obtain ⟨U, P, hU, _, hKU, htime, hα, hPe, hP, hpair⟩ :=
      lExponentialFamily_exists_terminal_adapted_frame hτmax hwindow A Z b hb hmax e he'
    have hi := lExponentialFamily_sharp_adapted_diagonal hM04 hL hτmax hwindow A Z b hb hmax
      hmin f O hO hqO hf hvalue hlower hsharp P U hU hKU htime hα hP hpair i
    rw [hPe i, hei] at hi
    rw [hR, ← hH]
    exact hi
  have hdiag (v : TangentSpace (𝓡 n) q) : R v v + H v v = g.inner q v v / (2 * b) := by
    by_cases hv : v = 0
    · subst v
      simp
    let u := normalize v
    have hu : g.inner q u u = 1 := by
      change ⟪u, u⟫ = (1 : ℝ)
      rw [real_inner_self_eq_norm_sq, norm_normalize hv]
      norm_num
    have hvrep : ‖v‖ • u = v := norm_smul_normalize v
    have hgdiag : g.inner q v v = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
    calc
      R v v + H v v = R (‖v‖ • u) (‖v‖ • u) + H (‖v‖ • u) (‖v‖ • u) := by rw [hvrep]
      _ = ‖v‖ ^ 2 * (R u u + H u u) := by
        simp only [map_smul, smul_apply, smul_eq_mul]
        ring
      _ = g.inner q v v / (2 * b) := by rw [hunit u hu, hgdiag]; ring
  have hRsymm (v w : TangentSpace (𝓡 n) q) : R v w = R w v := by
    rw [hR, hR]
    exact ((hM04.tensor_calculus n M g D).2.2.2.1 q v w 0 0).2.2.2
  have hHsymm (v w : TangentSpace (𝓡 n) q) : H v w = H w v := by
    rw [← hH, ← hH]
    have h := squareTime_hessian_symmetric_local F T τmax hτmax hwindow q c hctime
      f O hO hqO hf v w
    rwa [hc2] at h
  intro v w
  change D.ricci q v w + D.hessian f q v w = g.inner q v w / (2 * b)
  rw [← hR, hH]
  have hv := hdiag v
  have hw := hdiag w
  have hvw := hdiag (v + w)
  simp only [map_add, add_apply, hRsymm w v, hHsymm w v, g.symm q w v] at hvw
  field_simp [hb.ne'] at hv hw hvw ⊢
  nlinarith

end PoincareConjecture.Proofs.M09
