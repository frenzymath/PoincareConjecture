import PoincareConjecture.Proofs.M62.Sec19_1_SpacetimeCharts
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorField.Pullback










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Topology
open scoped Manifold ContDiff Bundle

noncomputable section

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

namespace SpacetimeCharts


theorem contMDiff_space (C : SpacetimeCharts n M a b) :
    ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞ (fun q : C.Point => q.1) := by
  let := C.chartedSpace
  exact contMDiff_fst.comp C.to_product_smooth


theorem contMDiff_clock (C : SpacetimeCharts n M a b) :
    ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞
      (fun q : C.Point => (q.2 : ℝ)) := by
  let := C.chartedSpace
  exact (contMDiff_subtype_val.comp contMDiff_snd).comp C.to_product_smooth



theorem split_mfderiv_from_product (C : SpacetimeCharts n M a b)
    (q : C.Point) (V : TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) q) :
    C.split q
        (mfderiv (M' := C.Point) ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1))
          (id : SpacetimeCarrier M a b → C.Point) q V) =
      (V.1, V.2) := by
  let := C.chartedSpace
  apply Prod.ext
  · rw [C.split_space]
    have h := mfderiv_comp_apply (f := (id : SpacetimeCarrier M a b → C.Point))
      (g := (Prod.fst : C.Point → M)) q
      (C.contMDiff_space.mdifferentiableAt (by simp))
      (C.from_product_smooth.mdifferentiableAt (by simp)) V
    simpa +instances only [Function.comp_def, id_eq, mfderiv_fst,
      ContinuousLinearMap.coe_fst'] using! h.symm
  · rw [C.split_time]
    have h := mfderiv_comp_apply (f := (id : SpacetimeCarrier M a b → C.Point))
      (g := fun p : C.Point => (p.2 : ℝ)) q
      (C.contMDiff_clock.mdifferentiableAt (by simp))
      (C.from_product_smooth.mdifferentiableAt (by simp)) V
    have ht := mfderiv_comp_apply
      (I := (𝓡 n).prod 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓘(ℝ, ℝ))
      (f := (Prod.snd : SpacetimeCarrier M a b → OpenTime a b))
      (g := (Subtype.val : OpenTime a b → ℝ)) q
      (contMDiff_subtype_val.mdifferentiableAt (n := ∞) (by simp))
      mdifferentiableAt_snd V
    rw [PoincareConjecture.Proofs.M11.mfderiv_openSubtype_val, mfderiv_snd] at ht
    exact h.symm.trans ht



theorem timeVector_smooth (C : SpacetimeCharts n M a b) :
    C.IsSmoothField C.timeVector := by
  let := C.chartedSpace
  have hreal : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ)).tangent ∞
      (fun t : ℝ => (⟨t, 1⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  have hinc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (Subtype.val : OpenTime a b → ℝ) := contMDiff_subtype_val
  have hinv (t : OpenTime a b) :
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (Subtype.val : OpenTime a b → ℝ) t).IsInvertible := by
    rw [PoincareConjecture.Proofs.M11.mfderiv_openSubtype_val]
    exact ⟨ContinuousLinearEquiv.refl ℝ ℝ, rfl⟩
  have hunit : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ)).tangent ∞
      (fun t : OpenTime a b => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) (OpenTime a b))) := by
    have h := hreal.mpullback_vectorField hinc hinv (by simp)
    apply h.congr
    intro t
    dsimp only [VectorField.mpullback]
    rw [PoincareConjecture.Proofs.M11.mfderiv_openSubtype_val]
    congr 1
    change (1 : ℝ) = (ContinuousLinearMap.id ℝ ℝ).inverse 1
    simp
  have hzero : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun q : SpacetimeCarrier M a b => (⟨q.1, 0⟩ : TangentBundle (𝓡 n) M)) :=
    (contMDiff_zeroSection ℝ (TangentSpace (𝓡 n) : M → Type _)).comp contMDiff_fst
  have hprod : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ))
      ((𝓡 n).prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun q : SpacetimeCarrier M a b =>
        (⟨q, (0, 1)⟩ : TangentBundle ((𝓡 n).prod 𝓘(ℝ, ℝ))
          (SpacetimeCarrier M a b))) :=
    contMDiff_equivTangentBundleProd_symm.comp (hzero.prodMk (hunit.comp contMDiff_snd))
  have h := ((C.from_product_smooth.contMDiff_tangentMap (m := ∞) (by simp)).comp
    hprod).comp C.to_product_smooth
  apply h.congr
  intro q
  dsimp only [Function.comp_apply, id_eq, tangentMap]
  rw [TotalSpace.mk_inj]
  apply (C.split q).injective
  erw [C.split_mfderiv_from_product]
  exact (C.split q).apply_symm_apply (0, 1)



theorem liftSpatialField_smooth_iff (C : SpacetimeCharts n M a b)
    (B : ℝ → (p : M) → TangentSpace (𝓡 n) p) :
    C.IsSmoothField (C.liftSpatialField B) ↔
      ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ))
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (fun q : SpacetimeCarrier M a b =>
          (⟨q.1, B q.2 q.1⟩ : TangentBundle (𝓡 n) M)) := by
  let := C.chartedSpace
  constructor
  · intro hB
    have h := ((C.contMDiff_space.contMDiff_tangentMap (m := ∞) (by simp)).comp
      hB).comp C.from_product_smooth
    apply h.congr
    intro q
    dsimp only [Function.comp_apply, id_eq, tangentMap]
    rw [TotalSpace.mk_inj]
    symm
    change mfderiv (𝓡 (n + 1)) (𝓡 n) (Prod.fst : C.Point → M) q
      (C.horizontal q (B q.2 q.1)) = B q.2 q.1
    rw [← C.split_space]
    exact congrArg Prod.fst ((C.split q).apply_symm_apply (B q.2 q.1, 0))
  · intro hB
    have hzero : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)).tangent ∞
        (fun q : SpacetimeCarrier M a b =>
          (⟨q.2, 0⟩ : TangentBundle 𝓘(ℝ, ℝ) (OpenTime a b))) :=
      (contMDiff_zeroSection ℝ (TangentSpace 𝓘(ℝ, ℝ) : OpenTime a b → Type _)).comp
        contMDiff_snd
    have hprod : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ))
        ((𝓡 n).prod 𝓘(ℝ, ℝ)).tangent ∞
        (fun q : SpacetimeCarrier M a b =>
          (⟨q, (B q.2 q.1, 0)⟩ : TangentBundle ((𝓡 n).prod 𝓘(ℝ, ℝ))
            (SpacetimeCarrier M a b))) :=
      contMDiff_equivTangentBundleProd_symm.comp (hB.prodMk hzero)
    have h := ((C.from_product_smooth.contMDiff_tangentMap (m := ∞) (by simp)).comp
      hprod).comp C.to_product_smooth
    apply h.congr
    intro q
    dsimp only [Function.comp_apply, id_eq, tangentMap]
    rw [TotalSpace.mk_inj]
    apply (C.split q).injective
    erw [C.split_mfderiv_from_product]
    exact (C.split q).apply_symm_apply (B q.2 q.1, 0)



theorem horizontal_time_decomposition (C : SpacetimeCharts n M a b)
    (q : C.Point) (V : TangentSpace (𝓡 (n + 1)) q) :
    C.horizontal q (C.split q V).1 + (C.split q V).2 • C.timeVector q = V := by
  apply (C.split q).injective
  simp [horizontal, timeVector]

end SpacetimeCharts

namespace SpacetimeData


theorem inner_horizontal {F : RicciFlow n M (Set.Icc a b)}
    (G : SpacetimeData F) (q : G.charts.Point)
    (V W : TangentSpace (𝓡 n) q.1) :
    G.metric.inner q (G.charts.horizontal q V) (G.charts.horizontal q W) =
      (F.metric q.2).inner q.1 V W := by
  simp [G.metric_eq, SpacetimeCharts.horizontal]



theorem inner_time {F : RicciFlow n M (Set.Icc a b)}
    (G : SpacetimeData F) (q : G.charts.Point)
    (V : TangentSpace (𝓡 (n + 1)) q) :
    G.metric.inner q V (G.charts.timeVector q) = (G.charts.split q V).2 := by
  simp [G.metric_eq, SpacetimeCharts.timeVector]


theorem time_unit {F : RicciFlow n M (Set.Icc a b)}
    (G : SpacetimeData F) (q : G.charts.Point) :
    G.metric.inner q (G.charts.timeVector q) (G.charts.timeVector q) = 1 := by
  rw [G.inner_time]
  simp [SpacetimeCharts.timeVector]

end SpacetimeData

end PoincareConjecture.M62
