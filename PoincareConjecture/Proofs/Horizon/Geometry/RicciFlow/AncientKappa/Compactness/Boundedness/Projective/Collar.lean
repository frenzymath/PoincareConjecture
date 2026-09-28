import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Topology
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Orientation.ProjectivePlane.Cover.Projection
import PoincareConjecture.Proofs.Horizon.Topology.Quotient.Coordinates








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology Manifold ContDiff

namespace PoincareConjecture



theorem exists_projectiveCylinderSlab_homeomorph
    {M : Type*} [TopologicalSpace M] (f : RoundCylinderSpace → M) {s : ℝ}
    (hf : IsLocalHomeomorphOn f (univ ×ˢ Ioo (-s) s))
    (hfiber : ∀ z ∈ univ ×ˢ Ioo (-s) s, ∀ w ∈ univ ×ˢ Ioo (-s) s,
      f z = f w ↔ w = z ∨ w = (-z.1, z.2)) :
    IsOpen (f '' (univ ×ˢ Ioo (-s) s)) ∧
      ∃ e : (RealProjectiveTwo × Ioo (-s) s) ≃ₜ
          (f '' (univ ×ˢ Ioo (-s) s)),
        ∀ (q : UnitTwoSphere) (t : Ioo (-s) s),
          (e (Quotient.mk realProjectiveTwoSetoid q, t)).val = f (q, t.val) := by
  let j : UnitTwoSphere × Ioo (-s) s → RoundCylinderSpace :=
    fun z => (z.1, z.2.val)
  have hj : IsLocalHomeomorph j :=
    (Topology.IsOpenEmbedding.id.prodMap isOpen_Ioo.isOpenEmbedding_subtypeVal).isLocalHomeomorph
  have hfj : IsLocalHomeomorph (f ∘ j) := by
    apply isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
    exact hf.comp hj.isLocalHomeomorphOn (fun z _ => ⟨mem_univ _, z.2.property⟩)
  have hrange : range (f ∘ j) = f '' (univ ×ˢ Ioo (-s) s) := by
    ext x
    constructor
    · rintro ⟨⟨q, t⟩, rfl⟩
      exact ⟨(q, t.val), ⟨mem_univ _, t.property⟩, rfl⟩
    · rintro ⟨⟨q, t⟩, ht, rfl⟩
      exact ⟨(q, ⟨t, ht.2⟩), rfl⟩
  refine ⟨hrange ▸ hfj.isOpenMap.isOpen_range, ?_⟩
  let F : C(UnitTwoSphere × Ioo (-s) s, f '' (univ ×ˢ Ioo (-s) s)) :=
    ⟨fun z => ⟨f (j z), ⟨j z, ⟨mem_univ _, z.2.property⟩, rfl⟩⟩,
      hfj.continuous.subtype_mk _⟩
  have hF : Topology.IsQuotientMap F := by
    have hFo : IsOpenMap F := hfj.isOpenMap.codRestrict
      (fun z => (show f (j z) ∈ f '' (univ ×ˢ Ioo (-s) s) from
        ⟨j z, ⟨mem_univ _, z.2.property⟩, rfl⟩))
    apply hFo.isQuotientMap F.continuous
    rintro ⟨x, ⟨q, t⟩, ht, rfl⟩
    exact ⟨(q, ⟨t, ht.2⟩), rfl⟩
  let Q : C(UnitTwoSphere × Ioo (-s) s, RealProjectiveTwo × Ioo (-s) s) :=
    ⟨Prod.map (Quotient.mk realProjectiveTwoSetoid) id,
      continuous_quotient_mk'.prodMap continuous_id⟩
  have hQ : Topology.IsQuotientMap Q := by
    apply IsOpenQuotientMap.isQuotientMap
    exact (show IsOpenQuotientMap (Quotient.mk realProjectiveTwoSetoid) from
      ⟨Quotient.mk_surjective, continuous_quotient_mk',
        Poincare.Topology.Orientation.ProjectivePlane.projectivePlaneProjection_isLocalHomeomorph.isOpenMap⟩).prodMap
      ⟨Function.surjective_id, continuous_id, IsOpenMap.id⟩
  have heq : ∀ z w, Q z = Q w ↔ F z = F w := by
    intro z w
    change (Quotient.mk realProjectiveTwoSetoid z.1, z.2) =
      (Quotient.mk realProjectiveTwoSetoid w.1, w.2) ↔ _
    simp only [Prod.mk.injEq, Subtype.ext_iff]
    change _ ↔ f (j z) = f (j w)
    rw [hfiber (j z) ⟨mem_univ _, z.2.property⟩ (j w) ⟨mem_univ _, w.2.property⟩]
    constructor
    · rintro ⟨hquot, ht⟩
      rcases Quotient.exact hquot with hq | hq
      · exact Or.inl (Prod.ext hq.symm ht.symm)
      · right
        apply Prod.ext
        · change w.1 = -z.1
          rw [hq, neg_neg]
        · exact ht.symm
    · rintro (h | h)
      · have hq := congrArg Prod.fst h
        have ht := congrArg Prod.snd h
        exact ⟨Quotient.sound (Or.inl hq.symm), ht.symm⟩
      · have hq := congrArg Prod.fst h
        have ht := congrArg Prod.snd h
        refine ⟨Quotient.sound (Or.inr ?_), ht.symm⟩
        change w.1 = -z.1 at hq
        rw [hq, neg_neg]
  refine ⟨hQ.homeomorphOfFibers hF heq, ?_⟩
  intro q t
  exact congrArg Subtype.val (hQ.homeomorphOfFibers_apply hF heq (q, t))




theorem exists_projectiveCylinderSlab_collar
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (f : RoundCylinderSpace → M) {s : ℝ} (hs : 0 < s)
    (hf : IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f
      (univ ×ˢ Ioo (-s) s))
    (hfiber : ∀ z ∈ univ ×ˢ Icc (-s) s, ∀ w ∈ univ ×ˢ Icc (-s) s,
      f z = f w ↔ w = z ∨ w = (-z.1, z.2)) :
    IsOpen (f '' (univ ×ˢ Ioo (-s) s)) ∧
      IsCompact (range (fun q : UnitTwoSphere => f (q, 0))) ∧
      IsConnected (range (fun q : UnitTwoSphere => f (q, 0))) ∧
      ∃ e : (RealProjectiveTwo × Ioo (-s) s) ≃ₜ
          (f '' (univ ×ˢ Ioo (-s) s)),
        (∀ (q : UnitTwoSphere) (t : Ioo (-s) s),
          (e (Quotient.mk realProjectiveTwoSetoid q, t)).val = f (q, t.val)) ∧
        range (fun q : RealProjectiveTwo =>
          (e (q, ⟨0, neg_lt_zero.mpr hs, hs⟩)).val) =
            range (fun q : UnitTwoSphere => f (q, 0)) := by
  obtain ⟨hopen, e, he⟩ := exists_projectiveCylinderSlab_homeomorph f
    hf.isLocalHomeomorphOn (fun z hz w hw =>
      hfiber z ⟨hz.1, hz.2.1.le, hz.2.2.le⟩ w ⟨hw.1, hw.2.1.le, hw.2.2.le⟩)
  have hc : Continuous (fun q : UnitTwoSphere => f (q, 0)) :=
    hf.isLocalHomeomorphOn.continuousOn.comp_continuous
      (continuous_id.prodMk continuous_const)
      (fun q => ⟨mem_univ q, neg_lt_zero.mpr hs, hs⟩)
  refine ⟨hopen, isCompact_range hc, isConnected_range hc, e, he, ?_⟩
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨q, rfl⟩ := Quotient.mk_surjective q
    exact ⟨q, (he q ⟨0, neg_lt_zero.mpr hs, hs⟩).symm⟩
  · rintro ⟨q, rfl⟩
    exact ⟨Quotient.mk realProjectiveTwoSetoid q, he q ⟨0, neg_lt_zero.mpr hs, hs⟩⟩

end PoincareConjecture
