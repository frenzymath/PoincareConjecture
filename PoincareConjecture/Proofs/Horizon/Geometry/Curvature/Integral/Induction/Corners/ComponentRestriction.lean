import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularFiberEquiv
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Isometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.ConnectedComponent
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace MeasureTheory
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Topology

theorem PoincareConjecture.RiemannianMetric.exists_openFiber_connectedComponent_restriction
    {m k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + k))) M]
    [IsManifold (𝓡 (m + k)) ∞ M]
    (g : PoincareConjecture.RiemannianMetric (m + k) M)
    {f : M → Fin k → ℝ} (hf : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) ∞ f)
    (U : Opens M) (hreg : ∀ x ∈ U, Function.Surjective
      (mfderiv (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) f x)) (c : Fin k → ℝ) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + k))) = m + k) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openFiberChartedSpace (m := m) hf U hreg c
    letI := isManifold_openFiber (m := m) hf U hreg c
    let L := openFiber f U c
    let incl := openFiberIncl f U c
    let gL := g.openRegularFiberMetric hf U hreg c
    ∀ p : L, ∃ V : Opens M,
      (V : Set M) ⊆ U ∧ incl ⁻¹' (V : Set M) = connectedComponent p ∧
      ∃ hregV : ∀ x ∈ V, Function.Surjective
        (mfderiv (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) f x),
        letI := openFiberChartedSpace (m := m) hf V hregV c
        letI := isManifold_openFiber (m := m) hf V hregV c
        let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin m)) p
        let gC := gL.connectedComponentMetric p
        let gV := g.openRegularFiberMetric hf V hregV c
        ∃ e : C ≃ₘ⟮𝓡 m, 𝓡 m⟯ openFiber f V c,
          (∀ x : C, openFiberIncl f V c (e x) = incl x.val) ∧
          ConnectedSpace (openFiber f V c) ∧
          (IsCompact (connectedComponent p) → CompactSpace (openFiber f V c)) ∧
          (∀ (x : C) (v w : TangentSpace (𝓡 m) x),
            gV.inner (e x) (mfderiv (𝓡 m) (𝓡 m) e x v)
              (mfderiv (𝓡 m) (𝓡 m) e x w) = gC.inner x v w) ∧
          (∀ x y : C, gV.edist (e x) (e y) = gC.edist x y) ∧
          MeasurePreserving e gC.volumeMeasure gV.volumeMeasure ∧
          (∀ x : C, gC.leviCivitaData.scalarCurvature x =
            gV.leviCivitaData.scalarCurvature (e x)) ∧
          ∀ F : openFiber f V c → ℝ,
            (∫ x, F (e x) ∂gC.volumeMeasure) = ∫ y, F y ∂gV.volumeMeasure := by
  classical
  dsimp only
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + k))) = m + k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openFiberChartedSpace (m := m) hf U hreg c
  let := isManifold_openFiber (m := m) hf U hreg c
  let L := openFiber f U c
  let incl := openFiberIncl f U c
  let gL := g.openRegularFiberMetric hf U hreg c
  intro p
  let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin m)) p
  obtain ⟨A, hA, hAC⟩ := (isEmbedding_openFiberIncl f U c).isInducing.isOpen_iff.mp C.isOpen
  let V : Opens M := ⟨A ∩ U, hA.inter U.isOpen⟩
  have hVU : (V : Set M) ⊆ U := inter_subset_right
  have hVC : incl ⁻¹' (V : Set M) = connectedComponent p := by
    ext x
    change (incl x ∈ A ∧ incl x ∈ U) ↔ x ∈ C
    have hx : incl x ∈ U := x.1.2
    rw [and_iff_left hx]
    change x ∈ incl ⁻¹' A ↔ x ∈ C
    rw [hAC]
    rfl
  have hregV : ∀ x ∈ V, Function.Surjective
      (mfderiv (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) f x) :=
    fun x hx => hreg x (hVU hx)
  refine ⟨V, hVU, hVC, hregV, ?_⟩
  let := openFiberChartedSpace (m := m) hf V hregV c
  let := isManifold_openFiber (m := m) hf V hregV c
  let LV := openFiber f V c
  let inclV := openFiberIncl f V c
  let gC := gL.connectedComponentMetric p
  let gV := g.openRegularFiberMetric hf V hregV c
  let E : C ≃ LV :=
    { toFun := fun x => ⟨⟨incl x.val, by
        change x.val ∈ incl ⁻¹' (V : Set M)
        rw [hVC]
        exact x.property⟩, x.val.property⟩
      invFun := fun y => ⟨⟨⟨inclV y, hVU y.1.2⟩, y.property⟩, by
        change (⟨⟨inclV y, hVU y.1.2⟩, y.property⟩ : L) ∈ connectedComponent p
        rw [← hVC]
        exact y.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e : C ≃ₘ⟮𝓡 m, 𝓡 m⟯ LV :=
    { E with
      contMDiff_toFun := by
        intro x
        apply (contMDiffAt_into_openFiber_iff (m := m) hf c V hregV E x).mpr
        exact ((contMDiff_openFiberIncl hf U hreg c).comp contMDiff_subtype_val) x
      contMDiff_invFun := by
        apply (ContMDiff.subtypeVal_comp_iff C E.symm).mp
        intro y
        apply (contMDiffAt_into_openFiber_iff (m := m) hf c U hreg
          (Subtype.val ∘ E.symm) y).mpr
        exact contMDiff_openFiberIncl hf V hregV c y }
  have hincl (x : C) : inclV (e x) = incl x.val := rfl
  have hmetric (x : C) (v w : TangentSpace (𝓡 m) x) :
      gC.inner x v w = gV.inner (e x) (mfderiv (𝓡 m) (𝓡 m) e x v)
        (mfderiv (𝓡 m) (𝓡 m) e x w) := by
    have hcV := mfderiv_comp x
      ((contMDiff_openFiberIncl hf V hregV c (e x)).mdifferentiableAt (by simp))
      (e.contMDiff.mdifferentiable (by simp) x)
    have hval : ContMDiff (𝓡 m) (𝓡 m) ∞ (Subtype.val : C → L) := contMDiff_subtype_val
    have hcC := mfderiv_comp x
      ((contMDiff_openFiberIncl hf U hreg c x.val).mdifferentiableAt (by simp))
      (hval.mdifferentiable (by simp) x)
    have heq : inclV ∘ e = incl ∘ (Subtype.val : C → L) := rfl
    change mfderiv (𝓡 m) (𝓡 (m + k)) (inclV ∘ e) x = _ at hcV
    change mfderiv (𝓡 m) (𝓡 (m + k)) (incl ∘ (Subtype.val : C → L)) x = _ at hcC
    rw [heq, hcC] at hcV
    change gL.inner x.val
      (mfderiv (𝓡 m) (𝓡 m) (Subtype.val : C → L) x v)
      (mfderiv (𝓡 m) (𝓡 m) (Subtype.val : C → L) x w) = _
    rw [openRegularFiberMetric_inner, openRegularFiberMetric_inner]
    have hv := congrArg (fun A => A v) hcV
    have hw := congrArg (fun A => A w) hcV
    exact congrArg₂ (fun v w => g.inner (incl x.val) v w) hv hw
  have hedist := gC.edist_eq_of_diffeomorph_metric_pullback gV e hmetric
  refine ⟨e, hincl, e.surjective.connectedSpace e.continuous, ?_,
    fun x v w => (hmetric x v w).symm, hedist, ?_, ?_, ?_⟩
  · intro hcompact
    let : CompactSpace C := isCompact_iff_compactSpace.mp hcompact
    exact e.toHomeomorph.compactSpace
  · exact gC.measurePreserving_volumeMeasure_of_edist_eq gV e.toEquiv hedist
  · intro x
    exact gC.leviCivitaData.scalarCurvature_eq_of_local_isometry gV.leviCivitaData
      isOpen_univ e.contMDiff.contMDiffOn (fun x _ => hmetric x) (mem_univ x)
  · intro F
    exact gC.integral_comp_equiv_volumeMeasure gV e.toEquiv hedist F
