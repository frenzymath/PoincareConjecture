import PoincareConjecture.Statements.M12HorizontalTheory
import PoincareConjecture.Proofs.M12.Geometry.Spacetime.Horizontal.Koszul
import PoincareConjecture.Proofs.M12.Geometry.Manifold.ContDiff.LinearMap











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Bundle Set Filter

universe u

namespace PoincareConjecture

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {S : ∀ t : ℝ, SpacetimeSliceGeometry F t}

local notation "H% " V => (fun q : F.Point => TotalSpace.mk'
  (EuclideanSpace ℝ (Fin n)) (E := F.Horizontal) q (V q))

private theorem horizontalInner_smoothAt
    {V W : HorizontalSection F} {p : F.Point}
    (hV : ContMDiffAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (H% V) p)
    (hW : ContMDiffAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (H% W) p) :
    ContMDiffAt (spacetimeModel n) 𝓘(ℝ) ∞
      (fun q => F.horizontalMetric.inner q (V q) (W q)) p := by
  exact (contMDiffAt_totalSpace.mp ((F.horizontalMetric.contMDiff p).clm_bundle_apply₂
    (F₃ := ℝ) (E₃ := fun _ : F.Point => ℝ) hV hW)).2

private theorem horizontalField_smoothAt
    {V : HorizontalSection F} {p : F.Point}
    (hV : ContMDiffAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (H% V) p) :
    ContMDiffAt (spacetimeModel n) (spacetimeModel n).tangent ∞
      (T% (horizontalSectionVectorField F V)) p := by
  have hi : ContMDiff
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (spacetimeModel n).tangent ∞
      (fun v : TotalSpace (EuclideanSpace ℝ (Fin n)) F.Horizontal =>
        TotalSpace.mk' (SpacetimeModelVector n)
          (E := (TangentSpace (spacetimeModel n) : F.Point → Type _)) v.proj v.2.val) :=
    F.horizontal_inclusion_smooth
  exact (hi _).comp p hV

private theorem horizontalBracket_smoothAt
    {V W : HorizontalSection F} {p : F.Point}
    (hV : ContMDiffAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (H% V) p)
    (hW : ContMDiffAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (H% W) p) :
    ContMDiffAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (H% (fun q => F.horizontalProjection q (VectorField.mlieBracket (spacetimeModel n)
        (horizontalSectionVectorField F V) (horizontalSectionVectorField F W) q))) p := by
  have : IsManifold (spacetimeModel n) (∞ + 1) F.Point := by
    simpa using (inferInstance : IsManifold (spacetimeModel n) ∞ F.Point)
  have : IsManifold (spacetimeModel n) (minSmoothness ℝ 2) F.Point := by
    simp only [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have hb := (horizontalField_smoothAt hV).mlieBracket_vectorField
    (horizontalField_smoothAt hW) (m := ⊤) (by simp)
  have hp : ContMDiff (spacetimeModel n).tangent
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun v : TangentBundle (spacetimeModel n) F.Point =>
        TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (E := F.Horizontal) v.proj
          (F.horizontalProjection v.proj v.2)) := F.horizontalProjection_smooth
  exact (hp _).comp p hb

private theorem horizontalInner_derivative_smoothAt
    {V W Z : HorizontalSection F} {p : F.Point}
    (hV : ContMDiffAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (H% V) p)
    (hW : ContMDiffAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (H% W) p)
    (hZ : ContMDiffAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (H% Z) p) :
    ContMDiffAt (spacetimeModel n) 𝓘(ℝ) ∞
      (fun q => mvfderiv (spacetimeModel n)
        (fun r => F.horizontalMetric.inner r (W r) (Z r)) q (V q).val) p := by
  have hf := horizontalInner_smoothAt hW hZ
  have hd := (hf.mfderiv_const (m := ∞) (by simp)).clm_apply_of_inCoordinates
    (horizontalField_smoothAt hV) hf
  rw [contMDiffAt_totalSpace] at hd
  simp only [id_eq] at hd
  convert hd.2 using 1
  funext q
  simp only [mvfderiv, ContinuousLinearMap.comp_apply]
  simp
  rfl



theorem rawLeafwiseCovariantDerivative_inner_smooth
    (hCoordinates : M12MetricPredecessors.{0} n)
    (D : LeafwiseLeviCivitaFamily F S) {T : SpacetimeIntervalSystem}
    (cover : SpacetimeGaugeCover F T)
    {V W Z : HorizontalSection F} {O : Set F.Point} (hO : IsOpen O)
    (hV : IsSmoothHorizontalSectionOn F V O)
    (hW : IsSmoothHorizontalSectionOn F W O)
    (hZ : IsSmoothHorizontalSectionOn F Z O) :
    ContMDiffOn (spacetimeModel n) 𝓘(ℝ) ∞
      (fun p => F.horizontalMetric.inner p (rawLeafwiseCovariantDerivative D W p (V p)) (Z p))
      O := by
  intro p hp
  have hv := hV.contMDiffAt (hO.mem_nhds hp)
  have hw := hW.contMDiffAt (hO.mem_nhds hp)
  have hz := hZ.contMDiffAt (hO.mem_nhds hp)
  have h := (((((horizontalInner_derivative_smoothAt hv hw hz).add
    (horizontalInner_derivative_smoothAt hw hz hv)).sub
    (horizontalInner_derivative_smoothAt hz hv hw)).add
    (horizontalInner_smoothAt (horizontalBracket_smoothAt hv hw) hz)).sub
    (horizontalInner_smoothAt (horizontalBracket_smoothAt hw hz) hv)).add
    (horizontalInner_smoothAt (horizontalBracket_smoothAt hz hv) hw)
  have hhalf := ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ).contDiff.contMDiff.contMDiffAt.comp p h
  apply (hhalf.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hO.mem_nhds hp] with q hq
  have hk := rawLeafwiseCovariantDerivative_koszul hCoordinates D cover hO hV hW hZ hq
  simp only [Function.comp_apply, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
    Pi.add_apply]
  linarith

private theorem horizontalMetric_inner_isInvertible (p : F.Point) :
    (F.horizontalMetric.inner p).IsInvertible := by
  let : RiemannianBundle F.Horizontal := ⟨F.horizontalMetric.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (F.Horizontal p) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n)) F.Horizontal p
  have heq : F.horizontalMetric.inner p =
      (InnerProductSpace.toDual ℝ (F.Horizontal p)).toContinuousLinearMap := by
    ext v w
    rfl
  rw [heq]
  exact ContinuousLinearMap.isInvertible_equiv
    (f := (InnerProductSpace.toDual ℝ (F.Horizontal p)).toContinuousLinearEquiv)

private theorem horizontalMetric_smoothAt_of_dual
    {Z : HorizontalSection F} {p : F.Point}
    (hZ : ContMDiffAt (spacetimeModel n) ((spacetimeModel n).prod
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
      (fun q => TotalSpace.mk' (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) q
        (F.horizontalMetric.inner q (Z q))) p) :
    ContMDiffAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (H% Z) p := by
  let E := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt E F.Horizontal p
  let e' := trivializationAt (E →L[ℝ] ℝ) (fun q => F.Horizontal q →L[ℝ] ℝ) p
  let G (q : F.Point) := ContinuousLinearMap.inCoordinates E F.Horizontal (E →L[ℝ] ℝ)
    (fun q => F.Horizontal q →L[ℝ] ℝ) p q p q (F.horizontalMetric.inner q)
  have hG : ContMDiffAt (spacetimeModel n) 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] ℝ)) ∞ G p :=
    (contMDiffAt_hom_bundle _).mp (F.horizontalMetric.contMDiff p) |>.2
  have hGinv (q : F.Point) (hq : q ∈ e.baseSet) (hq' : q ∈ e'.baseSet) :
      (G q).IsInvertible := by
    dsimp only [G]
    rw [ContinuousLinearMap.inCoordinates_eq hq hq']
    exact ContinuousLinearMap.isInvertible_equiv.comp
      ((horizontalMetric_inner_isInvertible q).comp ContinuousLinearMap.isInvertible_equiv)
  have hi := (hGinv p (FiberBundle.mem_baseSet_trivializationAt E F.Horizontal p)
    (FiberBundle.mem_baseSet_trivializationAt (E →L[ℝ] ℝ)
      (fun q => F.Horizontal q →L[ℝ] ℝ) p)).contDiffAt_map_inverse (n := ∞)
  have hresult := (hi.contMDiffAt.comp p hG).clm_apply (contMDiffAt_totalSpace.mp hZ).2
  rw [contMDiffAt_section]
  apply hresult.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt E F.Horizontal p),
    e'.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt (E →L[ℝ] ℝ)
      (fun q => F.Horizontal q →L[ℝ] ℝ) p)] with q hq hq'
  change (e ⟨q, Z q⟩).2 = (G q).inverse ((e' ⟨q, F.horizontalMetric.inner q (Z q)⟩).2)
  symm
  apply (hGinv q hq hq').inverse_apply_eq.mpr
  symm
  dsimp only [G]
  rw [ContinuousLinearMap.inCoordinates_eq hq hq']
  change (e'.continuousLinearEquivAt ℝ q hq')
    (F.horizontalMetric.inner q ((e.continuousLinearEquivAt ℝ q hq).symm
      ((e.continuousLinearEquivAt ℝ q hq) (Z q)))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rfl



theorem rawLeafwiseCovariantDerivative_apply_smooth
    (hCoordinates : M12MetricPredecessors.{0} n)
    (D : LeafwiseLeviCivitaFamily F S) {T : SpacetimeIntervalSystem}
    (cover : SpacetimeGaugeCover F T)
    {V W : HorizontalSection F} {O : Set F.Point} (hO : IsOpen O)
    (hV : IsSmoothHorizontalSectionOn F V O)
    (hW : IsSmoothHorizontalSectionOn F W O) :
    IsSmoothHorizontalSectionOn F (fun p => rawLeafwiseCovariantDerivative D W p (V p)) O := by
  intro p hp
  apply ContMDiffAt.contMDiffWithinAt
  apply horizontalMetric_smoothAt_of_dual
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  apply contMDiffAt_clm_of_apply_model
  intro v
  let E := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt E F.Horizontal p
  have hpe : p ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E F.Horizontal p
  let : TopologicalSpace (TotalSpace E (Bundle.Trivial F.Point E)) :=
    Bundle.Trivial.topologicalSpace F.Point E
  let : FiberBundle E (Bundle.Trivial F.Point E) := Bundle.Trivial.fiberBundle F.Point E
  let : VectorBundle ℝ E (Bundle.Trivial F.Point E) := Bundle.Trivial.vectorBundle ℝ F.Point E
  have hc : ContMDiff (spacetimeModel n) ((spacetimeModel n).prod 𝓘(ℝ, E)) ∞
      (fun q : F.Point => TotalSpace.mk' E (E := Bundle.Trivial F.Point E) q v) := by
    intro q
    rw [contMDiffAt_totalSpace]
    exact ⟨contMDiffAt_id, by simpa using contMDiffAt_const (c := v)⟩
  have hZ := (e.contMDiffOn_symmL (IB := spacetimeModel n) (n := ∞)).clm_bundle_apply
    hc.contMDiffOn
  have h := (rawLeafwiseCovariantDerivative_inner_smooth hCoordinates D cover
    (hO.inter e.open_baseSet) (hV.mono inter_subset_left) (hW.mono inter_subset_left)
    (hZ.mono inter_subset_right)).contMDiffAt
      ((hO.inter e.open_baseSet).mem_nhds ⟨hp, hpe⟩)
  change ContMDiffAt (spacetimeModel n) 𝓘(ℝ, ℝ) ∞
    (fun q => (ContinuousLinearMap.inCoordinates E F.Horizontal ℝ (fun _ : F.Point => ℝ)
      p q p q (F.horizontalMetric.inner q (rawLeafwiseCovariantDerivative D W q (V q)))) v) p
  have he : trivializationAt ℝ (fun _ : F.Point => ℝ) p =
    Bundle.Trivial.trivialization F.Point ℝ := rfl
  simpa only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    he, Bundle.Trivial.continuousLinearMapAt_trivialization,
    ContinuousLinearMap.id_apply] using h



theorem rawLeafwiseCovariantDerivative_smooth
    (hCoordinates : M12MetricPredecessors.{0} n)
    (D : LeafwiseLeviCivitaFamily F S) {T : SpacetimeIntervalSystem}
    (cover : SpacetimeGaugeCover F T)
    {O : Set F.Point} (hO : IsOpen O) {W : HorizontalSection F}
    (hW : IsSmoothHorizontalSectionOn F W O) :
    ContMDiffOn (spacetimeModel n)
      ((spacetimeModel n).prod
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ∞
      (fun p => TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        p (rawLeafwiseCovariantDerivative D W p)) O := by
  intro p hp
  apply ContMDiffAt.contMDiffWithinAt
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  apply contMDiffAt_clm_of_apply_model
  intro v
  let E := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt E F.Horizontal p
  have hpe : p ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E F.Horizontal p
  let : TopologicalSpace (TotalSpace E (Bundle.Trivial F.Point E)) :=
    Bundle.Trivial.topologicalSpace F.Point E
  let : FiberBundle E (Bundle.Trivial F.Point E) := Bundle.Trivial.fiberBundle F.Point E
  let : VectorBundle ℝ E (Bundle.Trivial F.Point E) := Bundle.Trivial.vectorBundle ℝ F.Point E
  have hc : ContMDiff (spacetimeModel n) ((spacetimeModel n).prod 𝓘(ℝ, E)) ∞
      (fun q : F.Point => TotalSpace.mk' E (E := Bundle.Trivial F.Point E) q v) := by
    intro q
    rw [contMDiffAt_totalSpace]
    exact ⟨contMDiffAt_id, by simpa using contMDiffAt_const (c := v)⟩
  have hV := (e.contMDiffOn_symmL (IB := spacetimeModel n) (n := ∞)).clm_bundle_apply
    hc.contMDiffOn
  have h := (rawLeafwiseCovariantDerivative_apply_smooth hCoordinates D cover
    (hO.inter e.open_baseSet) (hV.mono inter_subset_right) (hW.mono inter_subset_left)).contMDiffAt
      ((hO.inter e.open_baseSet).mem_nhds ⟨hp, hpe⟩)
  rw [contMDiffAt_section] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hpe] with q hq
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
  rw [e.symmL_apply hq]
  exact e.continuousLinearMapAt_apply_of_mem ℝ hq _

theorem rawHorizontalCovariantDerivative_apply_smoothAt
    (D : LeafwiseLeviCivitaFamily F S) {V : HorizontalSection F}
    {Z : (p : F.Point) → TangentSpace (spacetimeModel n) p} {p : F.Point}
    (hV : ContMDiffAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun q => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) q (V q)) p)
    (hL : ContMDiffAt (spacetimeModel n)
      ((spacetimeModel n).prod
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ∞
      (fun q => TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        q (rawLeafwiseCovariantDerivative D V q)) p)
    (hZ : ContMDiffAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n)) ∞
      (fun q => TotalSpace.mk' (SpacetimeModelVector n) q (Z q)) p) :
    ContMDiffAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun q => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) q
        (rawHorizontalCovariantDerivative D V q (Z q))) p := by
  have hp : ContMDiff
      ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun z : TangentBundle (spacetimeModel n) F.Point =>
        TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (E := F.Horizontal) z.proj
          (F.horizontalProjection z.proj z.2)) := F.horizontalProjection_smooth
  have hsp := hL.clm_bundle_apply ((hp _).comp p hZ)
  have ht : ContMDiff (spacetimeModel n) 𝓘(ℝ) ∞ F.timeFunction := F.time_smooth
  have hdt := ((ht p).mfderiv_const (m := ∞) (by simp)).clm_apply_of_inCoordinates
    (b₁ := id) (b₂ := F.timeFunction) hZ (ht p)
  have hreal := (contMDiffAt_totalSpace.mp hdt).2
  have hreal' : ContMDiffAt (spacetimeModel n) 𝓘(ℝ) ∞
      (fun q => mfderiv (spacetimeModel n) 𝓘(ℝ) F.timeFunction q (Z q)) p := by
    simpa using hreal
  exact hsp.add_section (hreal'.smul_section (horizontalTimeBracket_smooth hV))

theorem rawHorizontalCovariantDerivative_smoothAt
    (D : LeafwiseLeviCivitaFamily F S) {V : HorizontalSection F} {p : F.Point}
    (hV : ContMDiffAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun q => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) q (V q)) p)
    (hL : ContMDiffAt (spacetimeModel n)
      ((spacetimeModel n).prod
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ∞
      (fun q => TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        q (rawLeafwiseCovariantDerivative D V q)) p) :
    ContMDiffAt (spacetimeModel n)
      ((spacetimeModel n).prod
        𝓘(ℝ, SpacetimeModelVector n →L[ℝ] EuclideanSpace ℝ (Fin n))) ∞
      (fun q => TotalSpace.mk'
        (SpacetimeModelVector n →L[ℝ] EuclideanSpace ℝ (Fin n))
        q (rawHorizontalCovariantDerivative D V q)) p := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  apply contMDiffAt_clm_of_apply_model
  intro v
  let E := SpacetimeModelVector n
  let a := trivializationAt E (TangentSpace (spacetimeModel n) : F.Point → Type _) p
  let b := trivializationAt (EuclideanSpace ℝ (Fin n)) F.Horizontal p
  have hp : p ∈ a.baseSet := FiberBundle.mem_baseSet_trivializationAt _ _ _
  have hpb : p ∈ b.baseSet := FiberBundle.mem_baseSet_trivializationAt _ _ _
  letI : TopologicalSpace (TotalSpace E (Bundle.Trivial F.Point E)) :=
    Bundle.Trivial.topologicalSpace F.Point E
  letI : FiberBundle E (Bundle.Trivial F.Point E) := Bundle.Trivial.fiberBundle F.Point E
  letI : VectorBundle ℝ E (Bundle.Trivial F.Point E) := Bundle.Trivial.vectorBundle ℝ F.Point E
  have hc : ContMDiffAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, E)) ∞
      (fun q : F.Point => TotalSpace.mk' E (E := Bundle.Trivial F.Point E) q v) p := by
    rw [contMDiffAt_totalSpace]
    exact ⟨contMDiffAt_id, by simpa using contMDiffAt_const (c := v)⟩
  have hZ := (a.contMDiffAt_symmL (IB := spacetimeModel n) (n := ∞) hp).clm_bundle_apply hc
  have h := rawHorizontalCovariantDerivative_apply_smoothAt D hV hL hZ
  rw [contMDiffAt_section] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [a.open_baseSet.mem_nhds hp, b.open_baseSet.mem_nhds hpb] with q hq hqb
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
  rw [a.symmL_apply hq]
  exact b.continuousLinearMapAt_apply_of_mem ℝ hqb _

noncomputable def spacetimeHorizontalConnection_of_leafwise_smooth
    (D : LeafwiseLeviCivitaFamily F S)
    (hLeaf : ∀ U : Set F.Point, IsOpen U →
      ∀ V : HorizontalSection F, IsSmoothHorizontalSectionOn F V U →
        ContMDiffOn (spacetimeModel n)
          ((spacetimeModel n).prod
            𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ∞
          (fun p => TotalSpace.mk'
            (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
            p (rawLeafwiseCovariantDerivative D V p)) U) :
    SpacetimeHorizontalConnection D := by
  have hlocal (U : Set F.Point) (hU : IsOpen U) :
      ContMDiffCovariantDerivativeOn (I := spacetimeModel n) (V := F.Horizontal)
        (EuclideanSpace ℝ (Fin n)) ∞ (rawHorizontalConnection D).toFun U := by
    constructor
    intro V hV p hp
    exact (rawHorizontalCovariantDerivative_smoothAt D
      (hV.contMDiffAt (hU.mem_nhds hp))
      ((hLeaf U hU V hV).contMDiffAt (hU.mem_nhds hp))).contMDiffWithinAt
  refine
    { connection := rawHorizontalConnection D
      smooth := ⟨hlocal univ isOpen_univ⟩
      local_smooth := hlocal
      raw_eq := fun _ _ _ _ _ _ => rfl
      time_eq := ?_
      horizontal_eq := ?_
      metric_defect := ?_ }
  · intro U hU V hV p hp
    change (rawHorizontalCovariantDerivative D V p (F.timeVector p)).val = _
    rw [rawHorizontalCovariantDerivative_time]
    exact horizontalTimeBracket_val hU hV hp
  · intro U hU V hV p hp v
    exact rawHorizontalCovariantDerivative_horizontal D V p v
  · intro U hU V W hV hW p hp Z
    exact rawHorizontalCovariantDerivative_metric_defect D
      ((hV.contMDiffAt (hU.mem_nhds hp)).mdifferentiableAt (by simp))
      ((hW.contMDiffAt (hU.mem_nhds hp)).mdifferentiableAt (by simp)) Z



noncomputable def spacetimeHorizontalConnection
    (hCoordinates : M12MetricPredecessors.{0} n)
    (D : LeafwiseLeviCivitaFamily F S) {T : SpacetimeIntervalSystem}
    (cover : SpacetimeGaugeCover F T) : SpacetimeHorizontalConnection D :=
  spacetimeHorizontalConnection_of_leafwise_smooth D
    (fun _ hO _ hV => rawLeafwiseCovariantDerivative_smooth hCoordinates D cover hO hV)

end PoincareConjecture
