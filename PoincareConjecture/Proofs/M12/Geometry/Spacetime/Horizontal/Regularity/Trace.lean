import PoincareConjecture.Proofs.M12.Geometry.Spacetime.Horizontal.Regularity.Curvature
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.Trace
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Analysis.InnerProductSpace.GramMatrix








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

open scoped Manifold ContDiff Bundle BigOperators Topology
open Bundle Filter Set

universe u

namespace PoincareConjecture

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {S : ∀ t : ℝ, SpacetimeSliceGeometry F t}

private lemma contMDiffAt_matrix_det {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : F.Point → Matrix ι ι ℝ) (x : F.Point)
    (hG : ∀ i j, ContMDiffAt (spacetimeModel n) 𝓘(ℝ) ∞ (fun y => G y i j) x) :
    ContMDiffAt (spacetimeModel n) 𝓘(ℝ) ∞ (fun y => (G y).det) x := by
  simp only [Matrix.det_apply']
  apply ContMDiffAt.sum
  intro σ _
  exact contMDiffAt_const.mul (ContMDiffAt.prod fun i _ => hG (σ i) i)

private lemma contMDiffAt_matrix_inv_entry {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : F.Point → Matrix ι ι ℝ) (x : F.Point)
    (hG : ∀ i j, ContMDiffAt (spacetimeModel n) 𝓘(ℝ) ∞ (fun y => G y i j) x)
    (hx : (G x).det ≠ 0) (i j : ι) :
    ContMDiffAt (spacetimeModel n) 𝓘(ℝ) ∞ (fun y => (G y)⁻¹ i j) x := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_apply]
  apply ((contMDiffAt_matrix_det G x hG).inv₀ hx).mul
  apply contMDiffAt_matrix_det
  intro a b
  by_cases ha : a = j
  · subst a
    simpa using (contMDiffAt_const (I := spacetimeModel n) (x := x) (n := ∞)
      (c := (Pi.single i (1 : ℝ) : ι → ℝ) b))
  · simpa [Matrix.updateRow_apply, ha] using hG a b


noncomputable def horizontalTensorTrace
    (S : ∀ t : ℝ, SpacetimeSliceGeometry F t) {k : ℕ}
    (T : HorizontalCovariantTensorEvaluation F (k + 2)) :
    HorizontalCovariantTensorEvaluation F k := fun p v =>
  let x := spacetimeSlicePoint S p
  let j := (S (F.timeFunction p)).tangentEquiv x
  let b := (S (F.timeFunction p)).metricOnPoints.orthonormalBasis x
  ∑ i, T p (Fin.cons (j (b i)) (Fin.cons (j (b i)) v))


theorem IsSmoothHorizontalCovariantTensor.tensorTrace {k : ℕ}
    {T : HorizontalCovariantTensorEvaluation F (k + 2)}
    (hT : IsSmoothHorizontalCovariantTensor F T) :
    IsSmoothHorizontalCovariantTensor F (horizontalTensorTrace S T) := by
  classical
  constructor
  · intro p
    obtain ⟨A, hA⟩ := hT.1 p
    let x := spacetimeSlicePoint S p
    let j := (S (F.timeFunction p)).tangentEquiv x
    let b := (S (F.timeFunction p)).metricOnPoints.orthonormalBasis x
    refine ⟨∑ i, (A.curryLeft (j (b i))).curryLeft (j (b i)), fun v => ?_⟩
    simp only [horizontalTensorTrace, sum_apply, hA, MultilinearMap.curryLeft_apply]
    rfl
  · intro U hU V hV p hp
    let E := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt E F.Horizontal p
    let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let W := e.localFrame b
    have hep : p ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E F.Horizontal p
    let G : F.Point → Matrix (Fin n) (Fin n) ℝ :=
      fun q i j => F.horizontalMetric.inner q (W i q) (W j q)
    let A : F.Point → Matrix (Fin n) (Fin n) ℝ := fun q i j =>
      T q (Fin.cons (W i q) (Fin.cons (W j q) (fun a => V a q)))
    have hW i : IsSmoothHorizontalSectionOn F (W i) e.baseSet :=
      e.contMDiffOn_localFrame_baseSet ∞ b i
    have hG i j : ContMDiffAt (spacetimeModel n) 𝓘(ℝ) ∞ (fun q => G q i j) p :=
      (contMDiffAt_totalSpace.mp ((F.horizontalMetric.contMDiff p).clm_bundle_apply₂
        (F₃ := ℝ) (E₃ := Bundle.Trivial F.Point ℝ)
        ((hW i).contMDiffAt (e.open_baseSet.mem_nhds hep))
        ((hW j).contMDiffAt (e.open_baseSet.mem_nhds hep)))).2
    have hA i j : ContMDiffAt (spacetimeModel n) 𝓘(ℝ) ∞ (fun q => A q i j) p := by
      let VV : Fin (k + 2) → HorizontalSection F := fun a q =>
        Fin.cons (α := fun _ : Fin (k + 2) => F.Horizontal q) (W i q)
          (Fin.cons (α := fun _ : Fin (k + 1) => F.Horizontal q) (W j q)
            (fun a => V a q)) a
      have hh : ∀ a : Fin (k + 2), IsSmoothHorizontalSectionOn F (VV a)
          (U ∩ e.baseSet) := by
        intro a
        refine Fin.cases ((hW i).mono inter_subset_right)
          (fun a => Fin.cases ((hW j).mono inter_subset_right)
            (fun a => (hV a).mono inter_subset_left) a) a
      exact (hT.2 (U ∩ e.baseSet) (hU.inter e.open_baseSet) VV hh).contMDiffAt
        ((hU.inter e.open_baseSet).mem_nhds ⟨hp, hep⟩)
    let : RiemannianBundle F.Horizontal := ⟨F.horizontalMetric.toRiemannianMetric⟩
    have hdet : (G p).det ≠ 0 := by
      have h := Matrix.det_gram_ne_zero_iff_linearIndependent.mpr
        (e.basisAt b hep).linearIndependent
      change (Matrix.gram ℝ (fun i => W i p)).det ≠ 0
      simpa only [W, e.localFrame_apply_of_mem_baseSet b hep] using h
    have hinv := contMDiffAt_matrix_inv_entry G p hG hdet
    have hs : ContMDiffAt (spacetimeModel n) 𝓘(ℝ) ∞
        (fun q => ∑ i, ∑ j, (G q)⁻¹ i j * A q i j) p :=
      ContMDiffAt.sum fun i _ => ContMDiffAt.sum fun j _ => (hinv i j).mul (hA i j)
    apply ContMDiffAt.contMDiffWithinAt
    apply hs.congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds hep] with q hq
    let t := F.timeFunction q
    let : ChartedSpace (EuclideanSpace ℝ (Fin n)) (S t).Point := (S t).chartedSpace
    let x := spacetimeSlicePoint S q
    let j := (S t).tangentEquiv x
    let : RiemannianBundle (TangentSpace (𝓡 n) : (S t).Point → Type _) :=
      ⟨(S t).metricOnPoints.toRiemannianMetric⟩
    let c := (e.basisAt b hq).map j.symm.toLinearEquiv
    obtain ⟨B, hB⟩ := hT.1 q
    let C := (bilinearOfTensorCons B (fun a => V a q)).compl₁₂ j.toLinearMap j.toLinearMap
    have h := bilinear_sum_basis_eq_inverse_gram C c
      ((S t).metricOnPoints.orthonormalBasis x)
    have hj (v : F.Horizontal q) : j (j.symm v) = v := j.apply_symm_apply v
    have hc i : j (c i) = W i q := by
      change j (j.symm ((e.basisAt b hq) i)) = _
      rw [hj]
      exact (e.localFrame_apply_of_mem_baseSet b hq).symm
    have hg : Matrix.of (fun i l => (S t).metricOnPoints.inner x (c i) (c l)) = G q := by
      ext i l
      change (S t).metricOnPoints.inner x (c i) (c l) = G q i l
      rw [(S t).metric_eq]
      change F.horizontalMetric.inner q (j (c i)) (j (c l)) = G q i l
      rw [hc, hc]
    change (∑ i, B (Fin.cons (j ((S t).metricOnPoints.orthonormalBasis x i))
      (Fin.cons (j ((S t).metricOnPoints.orthonormalBasis x i)) (fun a => V a q)))) =
      ∑ i, ∑ l, (Matrix.of (fun i l => (S t).metricOnPoints.inner x (c i) (c l)))⁻¹ i l *
        B (Fin.cons (j (c i)) (Fin.cons (j (c l)) (fun a => V a q))) at h
    rw [hg] at h
    simp only [← hB, hc] at h
    simpa only [horizontalTensorTrace, A, t, x, j] using h


theorem IsSmoothHorizontalCovariantTensor.perm {k : ℕ}
    {T : HorizontalCovariantTensorEvaluation F k}
    (hT : IsSmoothHorizontalCovariantTensor F T) (σ : Equiv.Perm (Fin k)) :
    IsSmoothHorizontalCovariantTensor F (fun p v => T p (v ∘ σ)) := by
  constructor
  · intro p
    obtain ⟨A, hA⟩ := hT.1 p
    exact ⟨A.domDomCongr σ, fun v => hA _⟩
  · intro U hU V hV
    exact hT.2 U hU (fun i => V (σ i)) (fun i => hV (σ i))


theorem horizontalRicci_tensor_of_riemann
    (D : LeafwiseLeviCivitaFamily F S)
    (hR : IsSmoothHorizontalCovariantTensor F (k := 4)
      (fun p v => horizontalRiemann D p (v 0) (v 1) (v 2) (v 3))) :
    IsSmoothHorizontalCovariantTensor F (k := 2)
      (fun p v => horizontalRicci D p (v 0) (v 1)) := by
  let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective ![2, 0, 3, 1] (by decide)
  have h := (hR.perm σ).tensorTrace (S := S)
  convert h using 1
  funext p v
  let x := spacetimeSlicePoint S p
  let j := (S (F.timeFunction p)).tangentEquiv x
  let b := (S (F.timeFunction p)).metricOnPoints.orthonormalBasis x
  change (∑ i, (D.sliceConnection (F.timeFunction p)).curvatureTensor x
      (j.symm (v 0)) (b i) (j.symm (v 1)) (b i)) =
    ∑ i, (D.sliceConnection (F.timeFunction p)).curvatureTensor x
      (j.symm (v 0)) (j.symm (j (b i))) (j.symm (v 1)) (j.symm (j (b i)))
  simp only [ContinuousLinearEquiv.symm_apply_apply]


theorem horizontalScalarCurvature_smooth_of_ricci
    (D : LeafwiseLeviCivitaFamily F S)
    (hRic : IsSmoothHorizontalCovariantTensor F (k := 2)
      (fun p v => horizontalRicci D p (v 0) (v 1))) :
    ContMDiff (spacetimeModel n) 𝓘(ℝ) ∞ (horizontalScalarCurvature D) := by
  have h := hRic.tensorTrace (S := S) (k := 0)
  have hs := h.2 Set.univ isOpen_univ (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  rw [contMDiffOn_univ] at hs
  convert hs using 1
  funext p
  let x := spacetimeSlicePoint S p
  let j := (S (F.timeFunction p)).tangentEquiv x
  let b := (S (F.timeFunction p)).metricOnPoints.orthonormalBasis x
  change (∑ i, (D.sliceConnection (F.timeFunction p)).ricci x (b i) (b i)) =
    ∑ i, (D.sliceConnection (F.timeFunction p)).ricci x
      (j.symm (j (b i))) (j.symm (j (b i)))
  simp only [ContinuousLinearEquiv.symm_apply_apply]

end PoincareConjecture
