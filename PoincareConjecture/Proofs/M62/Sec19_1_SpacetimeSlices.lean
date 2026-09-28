import PoincareConjecture.Proofs.M62.Sec19_1_SpacetimeFrame










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M62.SpacetimeCharts

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}


theorem contMDiff_space_slice (C : SpacetimeCharts n M a b)
    (t : OpenTime a b) :
    ContMDiff (M' := C.Point) (𝓡 n) (𝓡 (n + 1)) ∞ (fun p : M => (p, t)) := by
  let := C.chartedSpace
  exact C.from_product_smooth.comp (contMDiff_id.prodMk contMDiff_const)



theorem mfderiv_space_slice (C : SpacetimeCharts n M a b)
    (t : OpenTime a b) (p : M) (V : TangentSpace (𝓡 n) p) :
    mfderiv (M' := C.Point) (𝓡 n) (𝓡 (n + 1)) (fun x : M => (x, t)) p V =
      C.horizontal (p, t) V := by
  let := C.chartedSpace
  have h := mfderiv_comp_apply
    (I := 𝓡 n) (I' := (𝓡 n).prod 𝓘(ℝ, ℝ)) (I'' := 𝓡 (n + 1))
    (f := fun x : M => ((x, t) : SpacetimeCarrier M a b))
    (g := (id : SpacetimeCarrier M a b → C.Point)) p
    (C.from_product_smooth.mdifferentiableAt (by simp))
    (mdifferentiableAt_id.prodMk mdifferentiableAt_const) V
  erw [mfderiv_prodMk mdifferentiableAt_id mdifferentiableAt_const] at h
  apply (C.split (p, t)).injective
  change C.split (p, t)
    (mfderiv (𝓡 n) (𝓡 (n + 1)) (id ∘ fun x : M => ((x, t) :
      SpacetimeCarrier M a b)) p V) = _
  rw [h]
  erw [C.split_mfderiv_from_product]
  simp [horizontal, mfderiv_id, mfderiv_const]
  rfl



theorem mvfderiv_space_slice (C : SpacetimeCharts n M a b)
    (f : C.Point → ℝ) (q : C.Point)
    (hf : MDifferentiableAt (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f q)
    (V : TangentSpace (𝓡 n) q.1) :
    mvfderiv (𝓡 (n + 1)) f q (C.horizontal q V) =
      mvfderiv (𝓡 n) (fun p => f (p, q.2)) q.1 V := by
  let := C.chartedSpace
  have h := mfderiv_comp_apply (f := fun p : M => ((p, q.2) : C.Point))
    (g := f) q.1 hf ((C.contMDiff_space_slice q.2).mdifferentiableAt (by simp)) V
  rw [C.mfderiv_space_slice] at h
  exact h.symm



theorem liftSpatialField_slice_smooth (C : SpacetimeCharts n M a b)
    (B : ℝ → (p : M) → TangentSpace (𝓡 n) p)
    (hB : C.IsSmoothField (C.liftSpatialField B)) (t : OpenTime a b) :
    ContMDiff (𝓡 n) (𝓡 n).tangent ∞ (T% (B t)) := by
  have h := (C.liftSpatialField_smooth_iff B).mp hB
  exact h.comp (contMDiff_id.prodMk (contMDiff_const (c := t)))



theorem liftSpatialField_slice_smoothAt (C : SpacetimeCharts n M a b)
    (B : ℝ → (p : M) → TangentSpace (𝓡 n) p) (q : C.Point)
    (hB : ContMDiffAt (𝓡 (n + 1)) (𝓡 (n + 1)).tangent ∞
      (T% (C.liftSpatialField B)) q) :
    ContMDiffAt (𝓡 n) (𝓡 n).tangent ∞ (T% (B q.2)) q.1 := by
  let := C.chartedSpace
  have h := ((C.contMDiff_space.contMDiff_tangentMap (m := ∞) (by simp)).contMDiffAt.comp
    q hB).comp q.1 (C.contMDiff_space_slice q.2 q.1)
  apply h.congr_of_eventuallyEq
  filter_upwards [] with p
  dsimp only [Function.comp_apply, tangentMap]
  rw [Bundle.TotalSpace.mk_inj]
  symm
  change mfderiv (𝓡 (n + 1)) (𝓡 n) (Prod.fst : C.Point → M) (p, q.2)
    (C.horizontal (p, q.2) (B q.2 p)) = B q.2 p
  rw [← C.split_space]
  exact congrArg Prod.fst ((C.split (p, q.2)).apply_symm_apply (B q.2 p, 0))

end PoincareConjecture.M62.SpacetimeCharts
