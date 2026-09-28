import PoincareConjecture.Proofs.M09.HessianTrace
import PoincareConjecture.Proofs.M09.LocalCenteredHessian

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem squareTime_hessian_exists_bilinear_local {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (f : M → ℝ) (O : Set M) (hO : IsOpen O) (hpO : p ∈ O)
    (hf : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f O) :
    ∃ H : E →L[ℝ] E →L[ℝ] ℝ,
      ∀ U V : E, (F.connection (T - s ^ 2)).hessian f p U V = H U V := by
  let e := chartAt E p
  let φ : E → ℝ := fun y ↦ f (e.symm y)
  let y0 := e p
  let V := e.target ∩ e.symm ⁻¹' O
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := contMDiffOn_chart_symm
  have hV : IsOpen V := he.continuousOn.isOpen_inter_preimage e.open_target hO
  have hy : y0 ∈ V := ⟨e.map_source (mem_chart_source E p), by
    change e.symm (e p) ∈ O
    rwa [e.left_inv (mem_chart_source E p)]⟩
  have hφ : ContDiffOn ℝ ∞ φ V :=
    (hf.comp (he.mono Set.inter_subset_left) (fun y hy ↦ hy.2)).contDiffOn
  have hD : DifferentiableAt ℝ (fderiv ℝ φ) y0 :=
    (((hφ.contDiffAt (hV.mem_nhds hy)).fderiv_right
      (m := ∞) (by simp)).differentiableAt (by simp))
  let C := coordinateConnectionBilinear (squareChartMetric F T p) (s, y0)
  let H : E →L[ℝ] E →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ φ) y0 -
    (ContinuousLinearMap.compL ℝ E E ℝ (fderiv ℝ φ y0)).comp C
  refine ⟨H, ?_⟩
  intro U W
  have hd : fderiv ℝ (fun y ↦ fderiv ℝ φ y W) y0 U =
      fderiv ℝ (fderiv ℝ φ) y0 U W := by
    have h := hD.hasFDerivAt.clm_apply (hasFDerivAt_const W y0)
    simpa using congrArg (fun L : E →L[ℝ] ℝ ↦ L U) h.fderiv
  rw [hessian_centeredCoordinates_local (F.connection (T - s ^ 2)) f p O hO hpO hf U W]
  change fderiv ℝ (fun y ↦ fderiv ℝ φ y W) y0 U -
    fderiv ℝ φ y0 ((F.connection (T - s ^ 2)).connection (chartVectorField p W) p U) = H U W
  rw [hd, ← squareChartConnection_at_center F T b hb hwindow p s hs U W]
  rfl

theorem squareTime_laplacian_orthonormal_trace_local {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (f : M → ℝ) (O : Set M) (hO : IsOpen O) (hpO : p ∈ O)
    (hf : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f O) {ι : Type*} [Fintype ι] :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric (T - s ^ 2)).toRiemannianMetric⟩
    ∀ e : OrthonormalBasis ι ℝ (TangentSpace (𝓡 n) p),
      (∑ i, (F.connection (T - s ^ 2)).hessian f p (e i) (e i)) =
        (F.connection (T - s ^ 2)).laplacian f p := by
  obtain ⟨H, hH⟩ := squareTime_hessian_exists_bilinear_local F T b hb hwindow p s hs f O hO hpO hf
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric (T - s ^ 2)).toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace (𝓡 n) : M → Type _) p
  let L : TangentSpace (𝓡 n) p →ₗ[ℝ] TangentSpace (𝓡 n) p →ₗ[ℝ] ℝ := {
    toFun := fun v ↦ (H v).toLinearMap
    map_add' := by intro v w; ext z; exact congrArg (fun B : E →L[ℝ] ℝ ↦ B z) (H.map_add v w)
    map_smul' := by intro c v; ext z; exact congrArg (fun B : E →L[ℝ] ℝ ↦ B z) (H.map_smul c v)
  }
  let B : TangentSpace (𝓡 n) p →L[ℝ] TangentSpace (𝓡 n) p →L[ℝ] ℝ :=
    ((LinearMap.toContinuousLinearMap : (TangentSpace (𝓡 n) p →ₗ[ℝ] ℝ) ≃ₗ[ℝ]
      (TangentSpace (𝓡 n) p →L[ℝ] ℝ)).toLinearMap.comp L).toContinuousLinearMap
  intro e
  have h := bilinear_trace_basis_eq B e ((F.metric (T - s ^ 2)).orthonormalBasis p)
  change (∑ i, H (e i) (e i)) =
    ∑ j, H ((F.metric (T - s ^ 2)).orthonormalBasis p j)
      ((F.metric (T - s ^ 2)).orthonormalBasis p j) at h
  change (∑ i, (F.connection (T - s ^ 2)).hessian f p (e i) (e i)) =
    ∑ j, (F.connection (T - s ^ 2)).hessian f p
      ((F.metric (T - s ^ 2)).orthonormalBasis p j)
      ((F.metric (T - s ^ 2)).orthonormalBasis p j)
  exact (Finset.sum_congr rfl (fun i _ ↦ hH (e i) (e i))).trans
    (h.trans (Finset.sum_congr rfl (fun j _ ↦ hH _ _)).symm)

end PoincareConjecture.Proofs.M09
