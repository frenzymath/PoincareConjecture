import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Projective.Covering
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cylinder.Sphere
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Sphere
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Geometry.Manifold.ContMDiff.Atlas













set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.StandardPuncturedProjectiveCover

variable {Q : Type u} [TopologicalSpace Q]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q]
  {p : RealProjectiveThree} {U : Set Q}
  (S : StandardPuncturedProjectiveCover Q p U)



private theorem isImmersion_sphere_lift
    {f : UnitTwoSphere → Q} (hf : Manifold.IsImmersion (𝓡 2) (𝓡 3) ∞ f)
    {F : UnitTwoSphere → UnitThreeSphere} (hF : Continuous F)
    (hmem : ∀ q, Quotient.mk' (F q) ≠ p) (hlift : ∀ q, S.cover (F q) = f q) :
    Manifold.IsImmersion (𝓡 2) (𝓡 3) ∞ F := by
  apply Manifold.IsImmersionOfComplement.isImmersion (F := hf.complement)
  intro x
  let h := hf.isImmersionOfComplement_complement x
  obtain ⟨φ, hx, heq⟩ := S.local_diffeomorph ⟨F x, hmem x⟩
  let s := F ⁻¹' φ.source
  have hs : IsOpen s := φ.open_source.preimage hF
  let d := h.domChart.restr s
  let b := φ.toOpenPartialHomeomorph.trans h.codChart
  have hdsource : d.source = h.domChart.source ∩ s :=
    h.domChart.restr_source' s hs
  have hb : b ∈ IsManifold.maximalAtlas (𝓡 3) ∞ UnitThreeSphere := by
    apply b.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).comp
        (φ.contMDiffOn.mono inter_subset_left) inter_subset_right
    · exact φ.symm.contMDiffOn.comp
        ((contMDiffOn_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).mono
          inter_subset_left) inter_subset_right
  have hsource (y : UnitTwoSphere) (hy : y ∈ d.source) : F y ∈ b.source := by
    rw [hdsource] at hy
    change F y ∈ φ.source ∧ φ (F y) ∈ h.codChart.source
    refine ⟨hy.2, ?_⟩
    rw [← heq hy.2, hlift]
    exact h.source_subset_preimage_source hy.1
  have hdx : x ∈ d.source := by
    rw [hdsource]
    exact ⟨h.mem_domChart_source, hx⟩
  apply Manifold.IsImmersionAtOfComplement.mk_of_charts h.equiv d b hdx
    (hsource x hdx) (restr_mem_maximalAtlas _ h.domChart_mem_maximalAtlas hs) hb hsource
  intro v hv
  have hv' : v ∈ d.target := by simpa using hv
  have hdv := d.map_target hv'
  rw [hdsource] at hdv
  change h.codChart (φ (F (d.symm v))) = h.equiv (v, 0)
  rw [← heq hdv.2, hlift]
  apply h.writtenInCharts
  simpa using hv'.1

private theorem isSmoothEmbedding_sphere_lift
    {f : UnitTwoSphere → Q} (hf : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {F : UnitTwoSphere → UnitThreeSphere} (hF : Continuous F)
    (hmem : ∀ q, Quotient.mk' (F q) ≠ p) (hlift : ∀ q, S.cover (F q) = f q) :
    Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ F := by
  have hi := S.isImmersion_sphere_lift hf.isImmersion hF hmem hlift
  refine ⟨hi, (hF.isClosedEmbedding ?_).isEmbedding⟩
  intro x y hxy
  exact hf.isEmbedding.injective
    ((hlift x).symm.trans ((congrArg S.cover hxy).trans (hlift y)))



theorem exists_smooth_embedded_sphere_lift
    (f : UnitTwoSphere → Q) (hf : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (hU : ∀ q, f q ∈ U) :
    ∃ F : UnitTwoSphere → UnitThreeSphere,
      Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ F ∧
      Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun q => -F q) ∧
      (∀ q, Quotient.mk' (F q) ≠ p) ∧
      (∀ q, S.cover (F q) = f q) ∧
      Disjoint (range F) (range (fun q => -F q)) ∧
      {q : UnitThreeSphere | Quotient.mk' q ≠ p ∧ S.cover q ∈ range f} =
        range F ∪ range (fun q => -F q) := by
  let : SimplyConnectedSpace UnitTwoSphere := Poincare.Topology.standardSphereSimplyConnected 0
  let : LocallyPathConnectedSpace UnitTwoSphere :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) UnitTwoSphere
  let fU : C(UnitTwoSphere, U) :=
    ⟨fun q => ⟨f q, hU q⟩, hf.contMDiff.continuous.subtype_mk _⟩
  let q₀ : UnitTwoSphere := Poincare.Topology.standardSpherePole 0
  obtain ⟨x₀, hx₀⟩ := S.restrictedCover_surjective (fU q₀)
  obtain ⟨L, ⟨_, hL⟩, _⟩ :=
    S.restrictedCover_isCoveringMap.existsUnique_continuousMap_lifts fU q₀ x₀ hx₀
  let F : UnitTwoSphere → UnitThreeSphere := fun q => (L q).val
  have hF : Continuous F := continuous_subtype_val.comp L.continuous
  have hmem (q : UnitTwoSphere) : Quotient.mk' (F q) ≠ p := (L q).property
  have hlift (q : UnitTwoSphere) : S.cover (F q) = f q :=
    congrArg Subtype.val (congrFun hL q)
  have hnegmem (q : UnitTwoSphere) : Quotient.mk' (-F q) ≠ p :=
    (PuncturedProjectiveSphere.antipode ⟨F q, hmem q⟩).property
  have hneglift (q : UnitTwoSphere) : S.cover (-F q) = f q :=
    ((S.fibers (-F q) (F q) (hnegmem q) (hmem q)).mpr (Or.inr rfl)).trans (hlift q)
  refine ⟨F, S.isSmoothEmbedding_sphere_lift hf hF hmem hlift,
    S.isSmoothEmbedding_sphere_lift hf hF.neg hnegmem hneglift,
    hmem, hlift, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    rintro z ⟨a, ha⟩ ⟨b, hb⟩
    have heq : F a = -F b := ha.trans hb.symm
    have hab : a = b := hf.isEmbedding.injective
      ((hlift a).symm.trans ((congrArg S.cover heq).trans (hneglift b)))
    subst b
    exact ne_neg_of_mem_unit_sphere ℝ (F a) heq
  · ext q
    constructor
    · rintro ⟨hq, x, hx⟩
      have heq : S.cover q = S.cover (F x) := hx.symm.trans (hlift x).symm
      rcases (S.fibers q (F x) hq (hmem x)).mp heq with h | h
      · exact Or.inl ⟨x, h.symm⟩
      · exact Or.inr ⟨x, h.symm⟩
    · rintro (⟨x, rfl⟩ | ⟨x, rfl⟩)
      · exact ⟨hmem x, x, (hlift x).symm⟩
      · exact ⟨hnegmem x, x, (hneglift x).symm⟩

end PoincareConjecture.StandardPuncturedProjectiveCover

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] {g : RiemannianMetric 3 M} (C : CapCertificate g)



theorem exists_boundary_sphere_lift
    (S : StandardPuncturedProjectiveCover M C.puncture C.carrier) :
    ∃ F : UnitTwoSphere → UnitThreeSphere,
      Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ F ∧
      Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun q => -F q) ∧
      (∀ q, Quotient.mk' (F q) ≠ C.puncture) ∧
      (∀ q, S.cover (F q) = C.boundary_neck.coordinate_map (q, 0)) ∧
      Disjoint (range F) (range (fun q => -F q)) ∧
      {q : UnitThreeSphere | Quotient.mk' q ≠ C.puncture ∧ S.cover q ∈ C.boundary_sphere} =
        range F ∪ range (fun q => -F q) := by
  have hrange : range (fun q : UnitTwoSphere => C.boundary_neck.coordinate_map (q, 0)) =
      C.boundary_sphere :=
    C.boundary_neck.centralSphere_range.trans C.boundary_eq_neck_sphere.symm
  have hU (q : UnitTwoSphere) : C.boundary_neck.coordinate_map (q, 0) ∈ C.carrier :=
    C.boundary_subset (hrange ▸ mem_range_self q)
  simpa only [hrange] using S.exists_smooth_embedded_sphere_lift
    (fun q => C.boundary_neck.coordinate_map (q, 0))
    C.boundary_neck.centralSphere_isSmoothEmbedding hU



theorem exists_projective_boundary_lift (hkind : C.model_kind = .puncturedProjective) :
    ∃ (S : StandardPuncturedProjectiveCover M C.puncture C.carrier)
      (F : UnitTwoSphere → UnitThreeSphere),
      IsCoveringMap S.restrictedCover ∧ IsProperMap S.restrictedCover ∧
      Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ F ∧
      Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun q => -F q) ∧
      (∀ q, Quotient.mk' (F q) ≠ C.puncture) ∧
      (∀ q, S.cover (F q) = C.boundary_neck.coordinate_map (q, 0)) ∧
      Disjoint (range F) (range (fun q => -F q)) ∧
      {q : UnitThreeSphere | Quotient.mk' q ≠ C.puncture ∧ S.cover q ∈ C.boundary_sphere} =
        range F ∪ range (fun q => -F q) := by
  obtain ⟨S⟩ := C.nonempty_projective_cover hkind
  obtain ⟨F, hF⟩ := C.exists_boundary_sphere_lift S
  exact ⟨S, F, S.restrictedCover_isCoveringMap, S.restrictedCover_isProperMap, hF⟩

end PoincareConjecture.CapCertificate
