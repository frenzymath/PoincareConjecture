import PoincareConjecture.Proofs.M12.Geometry.Spacetime.Horizontal.Regularity.Curvature
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.Norm
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.Algebra.Structures








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

open scoped Manifold ContDiff Bundle BigOperators Topology
open Bundle Set

universe u

namespace PoincareConjecture

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {S : ∀ t : ℝ, SpacetimeSliceGeometry F t}

private lemma smooth_matrix_det {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : F.Point → Matrix ι ι ℝ) (x : F.Point)
    (hG : ∀ i j, ContMDiffAt (spacetimeModel n) 𝓘(ℝ) ∞ (fun y => G y i j) x) :
    ContMDiffAt (spacetimeModel n) 𝓘(ℝ) ∞ (fun y => (G y).det) x := by
  simp only [Matrix.det_apply']
  apply ContMDiffAt.sum
  intro σ _
  exact contMDiffAt_const.mul (ContMDiffAt.prod fun i _ => hG (σ i) i)

private lemma smooth_matrix_inv {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : F.Point → Matrix ι ι ℝ) (x : F.Point)
    (hG : ∀ i j, ContMDiffAt (spacetimeModel n) 𝓘(ℝ) ∞ (fun y => G y i j) x)
    (hx : (G x).det ≠ 0) (i j : ι) :
    ContMDiffAt (spacetimeModel n) 𝓘(ℝ) ∞ (fun y => (G y)⁻¹ i j) x := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_apply]
  apply ((smooth_matrix_det G x hG).inv₀ hx).mul
  apply smooth_matrix_det
  intro a b
  by_cases ha : a = j
  · subst a
    simpa using (contMDiffAt_const (I := spacetimeModel n) (x := x) (n := ∞)
      (c := (Pi.single i (1 : ℝ) : ι → ℝ) b))
  · simpa [Matrix.updateRow_apply, ha] using hG a b

private theorem sum_fin_cons {ι : Type*} [Fintype ι] {d : ℕ}
    (f : (Fin (d + 1) → ι) → ℝ) :
    (∑ p, f p) = ∑ a, ∑ q, f (Fin.cons a q) := by
  calc
    (∑ p, f p) = ∑ p : ι × (Fin d → ι), f (Fin.cons p.1 p.2) :=
      Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (d + 1) => ι)).symm _ _
        (fun p => congrArg f (Fin.cons_self_tail p).symm)
    _ = _ := Fintype.sum_prod_type _

private theorem horizontalCurvatureNormSq_inverse_gram
    (D : LeafwiseLeviCivitaFamily F S) (p : F.Point)
    (A : MultilinearMap ℝ (fun _ : Fin 4 => F.Horizontal p) ℝ)
    (hA : ∀ v, horizontalRiemann D p (v 0) (v 1) (v 2) (v 3) = A v)
    (b : Module.Basis (Fin n) ℝ (F.Horizontal p)) :
    horizontalCurvatureNormSq D p =
      ∑ i : Fin 4 → Fin n, ∑ j : Fin 4 → Fin n,
        (∏ r, (Matrix.of (fun a c => F.horizontalMetric.inner p (b a) (b c)))⁻¹
          (i r) (j r)) *
        (A (fun r => b (i r)) * A (fun r => b (j r))) := by
  let t := F.timeFunction p
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) (S t).Point := (S t).chartedSpace
  let : RiemannianBundle (TangentSpace (𝓡 n) : (S t).Point → Type _) :=
    ⟨(S t).metricOnPoints.toRiemannianMetric⟩
  let x := spacetimeSlicePoint S p
  let j := (S t).tangentEquiv x
  let B := A.compLinearMap (fun _ => j.toLinearMap)
  let c := b.map j.symm.toLinearEquiv
  let o := (S t).metricOnPoints.orthonormalBasis x
  have h := multilinear_sum_mul_eq_inverse_gram B B c o
  have hgram : (Matrix.of (fun a d => inner ℝ (c a) (c d))) =
      Matrix.of (fun a d => F.horizontalMetric.inner p (b a) (b d)) := by
    ext a d
    change (S t).metricOnPoints.inner x (j.symm (b a)) (j.symm (b d)) = _
    rw [(S t).metric_eq]
    simp only [j, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  rw [hgram] at h
  have hB (v : Fin 4 → TangentSpace (𝓡 n) x) : B v =
      (D.sliceConnection t).curvatureTensor x (v 0) (v 1) (v 2) (v 3) := by
    rw [show B v = A (fun r => j (v r)) from rfl, ← hA]
    simp only [horizontalRiemann, j, t, x, ContinuousLinearEquiv.symm_apply_apply]
  have hBc (a : Fin 4 → Fin n) : B (fun r => c (a r)) = A (fun r => b (a r)) := by
    change A (fun r => j (j.symm (b (a r)))) = _
    simp only [ContinuousLinearEquiv.apply_symm_apply]
  simp_rw [hBc] at h
  rw [← h]
  simp_rw [hB, ← pow_two]
  rw [sum_fin_cons]
  simp only [sum_fin_cons, Fin.cons_zero, Fintype.sum_unique]
  unfold horizontalCurvatureNormSq horizontalCurvatureNorm LeviCivitaData.curvatureTensorNorm
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)


theorem horizontalCurvatureNormSq_smooth_of_riemann
    (D : LeafwiseLeviCivitaFamily F S)
    (hR : IsSmoothHorizontalCovariantTensor F (k := 4)
      (fun p v => horizontalRiemann D p (v 0) (v 1) (v 2) (v 3))) :
    ContMDiff (spacetimeModel n) 𝓘(ℝ) ∞ (horizontalCurvatureNormSq D) := by
  classical
  let : RiemannianBundle F.Horizontal := ⟨F.horizontalMetric.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle (spacetimeModel n) ∞
      (EuclideanSpace ℝ (Fin n)) F.Horizontal :=
    ⟨F.horizontalMetric.inner, F.horizontalMetric.contMDiff, fun _ _ _ => rfl⟩
  intro p
  let E := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt E F.Horizontal p
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let V := e.localFrame b
  let G : F.Point → Matrix (Fin n) (Fin n) ℝ := fun q i j =>
    F.horizontalMetric.inner q (V i q) (V j q)
  let R : F.Point → (Fin 4 → Fin n) → ℝ := fun q a =>
    horizontalRiemann D q (V (a 0) q) (V (a 1) q) (V (a 2) q) (V (a 3) q)
  have hp : p ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E F.Horizontal p
  have hV (i : Fin n) : IsSmoothHorizontalSectionOn F (V i) e.baseSet :=
    e.contMDiffOn_localFrame_baseSet ∞ b i
  have hG (i j) : ContMDiffAt (spacetimeModel n) 𝓘(ℝ) ∞ (fun q => G q i j) p :=
    ((hV i).contMDiffAt (e.open_baseSet.mem_nhds hp)).inner_bundle
      ((hV j).contMDiffAt (e.open_baseSet.mem_nhds hp))
  have hR' (a : Fin 4 → Fin n) :
      ContMDiffAt (spacetimeModel n) 𝓘(ℝ) ∞ (fun q => R q a) p :=
    (hR.2 e.baseSet e.open_baseSet (fun r => V (a r)) (fun r => hV (a r))).contMDiffAt
      (e.open_baseSet.mem_nhds hp)
  have hdet : (G p).det ≠ 0 := by
    have hb := (e.basisAt b hp).linearIndependent
    change (Matrix.gram ℝ (fun i => V i p)).det ≠ 0
    apply Matrix.det_gram_ne_zero_iff_linearIndependent.mpr
    simpa only [V, e.localFrame_apply_of_mem_baseSet b hp] using hb
  have hinv := smooth_matrix_inv G p hG hdet
  have hs : ContMDiffAt (spacetimeModel n) 𝓘(ℝ) ∞
      (fun q => ∑ i : Fin 4 → Fin n, ∑ j : Fin 4 → Fin n,
        (∏ r, (G q)⁻¹ (i r) (j r)) * (R q i * R q j)) p := by
    exact ContMDiffAt.sum fun i _ => ContMDiffAt.sum fun j _ =>
      (ContMDiffAt.prod fun r _ => hinv (i r) (j r)).mul ((hR' i).mul (hR' j))
  apply hs.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hp] with q hq
  obtain ⟨A, hA⟩ := hR.1 q
  have h := horizontalCurvatureNormSq_inverse_gram D q A hA (e.basisAt b hq)
  have hg : Matrix.of (fun a c => F.horizontalMetric.inner q
      (e.basisAt b hq a) (e.basisAt b hq c)) = G q := by
    ext a c
    simp only [G, V, Matrix.of_apply, e.localFrame_apply_of_mem_baseSet b hq]
  rw [hg] at h
  simpa only [← e.localFrame_apply_of_mem_baseSet b hq, ← hA, V, R] using h

end PoincareConjecture
