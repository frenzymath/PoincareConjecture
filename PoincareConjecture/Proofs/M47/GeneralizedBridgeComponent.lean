import PoincareConjecture.Proofs.M47.GeneralizedBridgeIsometry
import PoincareConjecture.Proofs.M47.GeneralizedBridgeTopology
import PoincareConjecture.Proofs.M34.Standard.CapIsometryGeometry
import PoincareConjecture.Proofs.M34.Standard.CapIsometryScalar










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M47

section Isometry

variable {M X : Type u} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
  [T3Space M] [T3Space X]
  {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 X}



noncomputable def metricIsometry_pullback_C_component
    (f : Diffeomorph (𝓡 3) (𝓡 3) M X ∞) (hf : MetricHomothety g h f 1)
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {C : ℝ}
    (N : SingularCComponent h D' C) : SingularCComponent g D C := by
  let : T25Space M := T3Space.t25Space
  let : T2Space M := T25Space.t2Space
  let : T25Space X := T3Space.t25Space
  let : T2Space X := T25Space.t2Space
  have hi := metricHomothety_one_symm f hf
  have himage (U : Set X) : f.symm '' U = f ⁻¹' U :=
    f.symm.toEquiv.image_eq_preimage_symm U
  have hscalar (x : M) : D.scalarCurvature x = D'.scalarCurvature (f x) :=
    (M34.metricIsometry_scalar f hf D D' x).symm
  have hsup : scalarCurvatureSupOn g D (f ⁻¹' N.carrier) =
      scalarCurvatureSupOn h D' N.carrier := by
    rw [← himage]
    exact M34.metricIsometry_scalarSup f.symm hi _ _ N.carrier
  have hdiam : intrinsicDiameter g (f ⁻¹' N.carrier) = intrinsicDiameter h N.carrier := by
    rw [← himage]
    exact M34.metricIsometry_intrinsicDiameter _ _ f.symm hi N.carrier
  have hrange : range (fun x : f ⁻¹' N.carrier =>
      D.scalarCurvature x.val ^ (-1 / 2 : ℝ)) =
      range (fun x : N.carrier => D'.scalarCurvature x.val ^ (-1 / 2 : ℝ)) := by
    ext r
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨⟨f x.val, x.property⟩, ?_⟩
      change D'.scalarCurvature (f x.val) ^ (-1 / 2 : ℝ) = D.scalarCurvature x.val ^ (-1 / 2 : ℝ)
      rw [hscalar]
    · rintro ⟨x, rfl⟩
      refine ⟨⟨f.symm x.val, ?_⟩, ?_⟩
      · change f (f.symm x.val) ∈ N.carrier
        rw [f.apply_symm_apply]
        exact x.property
      change D.scalarCurvature (f.symm x.val) ^ (-1 / 2 : ℝ) =
        D'.scalarCurvature x.val ^ (-1 / 2 : ℝ)
      rw [hscalar, f.apply_symm_apply]
  have hpair (x : M) (v w : TangentSpace (𝓡 3) x)
      (hvw : LeviCivitaData.IsOrthonormalPair g x v w) :
      LeviCivitaData.IsOrthonormalPair h (f x)
        (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) := by
    unfold LeviCivitaData.IsOrthonormalPair
    rw [hf, hf, hf]
    simpa only [LeviCivitaData.IsOrthonormalPair, one_mul] using hvw
  have hsection (x : M) (v w : TangentSpace (𝓡 3) x) :
      D'.sectionalCurvature (f x)
        (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) =
          D.sectionalCurvature x v w := by
    simpa only [div_one] using M13.homothety_sectionalCurvature_eq _ _ f 1 zero_lt_one hf
      D D' x v w
  refine {
    constant_pos := N.constant_pos
    basepoint := f.symm N.basepoint
    carrier := f ⁻¹' N.carrier
    component_eq := ?_
    compact := by rw [← himage]; exact N.compact.image f.symm.continuous
    topology := ?_
    positive_sectional := fun x hx v w hvw =>
      (hsection x v w) ▸ N.positive_sectional (f x) hx _ _ (hpair x v w hvw)
    sectional_lower := ?_
    diameter_lower := by rw [hrange, hdiam]; exact N.diameter_lower
    diameter_upper := by rw [hrange, hdiam]; exact N.diameter_upper
  }
  · rw [← himage, N.component_eq]
    exact diffeomorph_image_connectedComponent f.symm N.basepoint
  · rcases N.topology with hK | hK
    · exact Or.inl ⟨(himage N.carrier) ▸
        diffeomorph_image_closed_certificate f.symm (Classical.choice hK)⟩
    · exact Or.inr ⟨(himage N.carrier) ▸
        diffeomorph_image_closed_certificate f.symm (Classical.choice hK)⟩
  · intro x hx v w hvw
    rw [hsup, ← hsection x v w]
    exact N.sectional_lower (f x) hx _ _ (hpair x v w hvw)

end Isometry

variable {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
  (H : M33RegularHistoryData W) {t : ℝ} (ht : t ∈ H.generalized.interval)
  (hregular : t ∉ F.surgery_times)

include hregular



theorem regular_history_component_control {epsilon C : ℝ}
    (x : (H.generalized.slice t).carrier)
    (N : SingularCComponent (F.metric t) (F.connection t) C)
    (hx : H.history.forward t ht x ∈ N.carrier) :
    Nonempty (GeneralizedCanonicalControl (F := H.generalized) t x epsilon C) := by
  let f := regular_history_slice_diffeomorph H t ht hregular
  have hf : MetricHomothety (H.generalized.metric t) (F.metric t) f 1 := by
    intro y v w
    change (F.metric t).inner (H.history.forward t ht y)
      (mfderiv (𝓡 3) (𝓡 3) (H.history.forward t ht) y v)
      (mfderiv (𝓡 3) (𝓡 3) (H.history.forward t ht) y w) = _
    rw [H.history.metric_pullback, one_mul]
  exact ⟨GeneralizedCanonicalControl.component
    (metricIsometry_pullback_C_component f hf (H.generalized.connection t) (F.connection t) N) hx⟩

end PoincareConjecture.M47
