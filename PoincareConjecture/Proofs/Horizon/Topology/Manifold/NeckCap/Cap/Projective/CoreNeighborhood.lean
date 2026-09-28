import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Projective.ExteriorComponents
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.CollaredDomain
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.SphereCharts
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.BallImages

noncomputable section
set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} (C : CapCertificate g)
  (S : StandardPuncturedProjectiveCover M C.puncture C.carrier)

theorem exists_projective_exterior_boundary_collar
    (a : UnitThreeSphere) (ha : Quotient.mk' a = C.puncture) :
    let A := connectedComponentIn (C.projectiveClosedCoreLift S)ᶜ a
    ∃ e : OpenPartialHomeomorph RoundCylinderSpace UnitThreeSphere,
      e.source = C.boundary_neck.cylinderDomain ∧
      ContMDiffOn CylModel (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) CylModel ∞ e.symm e.target ∧
      (∀ z ∈ e.source, Quotient.mk' (e z) ≠ C.puncture) ∧
      (∀ z ∈ e.source, S.cover (e z) = C.boundary_neck.coordinate_map z) ∧
      frontier A = range (fun q : UnitTwoSphere => e (q, 0)) := by
  obtain ⟨F, hF, _, hFmem, hFlift, hfront, _⟩ :=
    C.exists_projective_exterior_frontier_sphere S a ha
  obtain ⟨e, hes, he, hei, hmem, hlift, _, _⟩ :=
    C.exists_smooth_projective_boundary_collar S
  have hzero (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ e.source := by
    rw [hes]
    exact ⟨mem_univ _, neg_lt_zero.mpr (inv_pos.mpr C.boundary_neck.epsilon_pos),
      inv_pos.mpr C.boundary_neck.epsilon_pos⟩
  have hE := Poincare.isSmoothEmbedding_collar_center e he hei hzero
  let f : UnitTwoSphere → PuncturedProjectiveSphere C.puncture :=
    fun q => ⟨F q, hFmem q⟩
  let k : UnitTwoSphere → PuncturedProjectiveSphere C.puncture :=
    fun q => ⟨e (q, 0), hmem _ (hzero q)⟩
  have hf : Continuous f := hF.contMDiff.continuous.subtype_mk _
  have hk : Continuous k := hE.contMDiff.continuous.subtype_mk _
  have hcomp : S.restrictedCover ∘ f = S.restrictedCover ∘ k := by
    funext q
    apply Subtype.ext
    exact (hFlift q).trans (hlift _ (hzero q)).symm
  let q₀ := Poincare.Topology.standardSpherePole 0
  have hsame := S.fibers (F q₀) (e (q₀, 0)) (hFmem q₀) (hmem _ (hzero q₀))
  have hbase : S.cover (F q₀) = S.cover (e (q₀, 0)) :=
    (hFlift q₀).trans (hlift _ (hzero q₀)).symm
  rcases hsame.mp hbase with hbase | hbase
  · have hfk := S.restrictedCover_isCoveringMap.eq_of_comp_eq hf hk hcomp q₀ (Subtype.ext hbase)
    refine ⟨e, hes, he, hei, hmem, hlift, ?_⟩
    rw [hfront]
    congr 1
    funext q
    exact congrArg Subtype.val (congrFun hfk q)
  · let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
    let J : Diffeomorph (𝓡 3) (𝓡 3) UnitThreeSphere UnitThreeSphere ∞ := {
      toEquiv := Equiv.neg UnitThreeSphere
      contMDiff_toFun := contMDiff_neg_sphere
      contMDiff_invFun := contMDiff_neg_sphere }
    let d := e.trans J.toHomeomorph.toOpenPartialHomeomorph
    have hds : d.source = e.source := by simp [d]
    have hncomp : S.restrictedCover ∘ f =
        S.restrictedCover ∘ (PuncturedProjectiveSphere.antipode ∘ k) := by
      funext q
      apply Subtype.ext
      have hn := (PuncturedProjectiveSphere.antipode (k q)).property
      exact (congrArg Subtype.val (congrFun hcomp q)).trans
        ((S.fibers (-e (q, 0)) (e (q, 0)) hn (hmem _ (hzero q))).mpr (Or.inr rfl)).symm
    have hfk := S.restrictedCover_isCoveringMap.eq_of_comp_eq hf
      ((PuncturedProjectiveSphere.continuous_antipode C.puncture).comp hk)
      hncomp q₀ (Subtype.ext hbase)
    refine ⟨d, hds.trans hes, ?_, ?_, ?_, ?_, ?_⟩
    · exact J.contMDiff.comp_contMDiffOn (he.mono (hds ▸ Subset.rfl))
    · exact hei.comp J.symm.contMDiff.contMDiffOn inter_subset_right
    · intro z hz
      exact (PuncturedProjectiveSphere.antipode ⟨e z, hmem z (hds ▸ hz)⟩).property
    · intro z hz
      have hn := (PuncturedProjectiveSphere.antipode ⟨e z, hmem z (hds ▸ hz)⟩).property
      exact ((S.fibers (-e z) (e z) hn (hmem z (hds ▸ hz))).mpr (Or.inr rfl)).trans
        (hlift z (hds ▸ hz))
    · rw [hfront]
      congr 1
      funext q
      exact congrArg Subtype.val (congrFun hfk q)

theorem exists_oriented_projective_exterior_collar
    (a : UnitThreeSphere) (ha : Quotient.mk' a = C.puncture) :
    let A := connectedComponentIn (C.projectiveClosedCoreLift S)ᶜ a
    ∃ δ : ℝ, 0 < δ ∧
      ∃ e : OpenPartialHomeomorph RoundCylinderSpace UnitThreeSphere,
        e.source = univ ×ˢ Ioo (-δ) δ ∧
        ContMDiffOn CylModel (𝓡 3) ∞ e e.source ∧
        ContMDiffOn (𝓡 3) CylModel ∞ e.symm e.target ∧
        (∀ y ∈ e.target, Quotient.mk' y ≠ C.puncture) ∧
        frontier A = range (fun q : UnitTwoSphere => e (q, 0)) ∧
        (∀ y ∈ e.target, y ∈ closure A ↔ 0 ≤ (e.symm y).2) ∧
        ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
          ∀ z ∈ e.source,
            S.cover (e z) = C.boundary_neck.coordinate_map (z.1, σ * z.2) := by
  let K := C.projectiveClosedCoreLift S
  let A := connectedComponentIn Kᶜ a
  let B := Neg.neg '' A
  obtain ⟨e, hes, he, hei, hmem, hlift, hfront⟩ :=
    C.exists_projective_exterior_boundary_collar S a ha
  obtain ⟨hA, hcA, hdis, hcover, haA, _⟩ := C.projectiveClosedCoreLift_exterior_components S a ha
  have hB : IsOpen B := (Homeomorph.neg UnitThreeSphere).isOpenMap _ hA
  have hdiscl : Disjoint (closure A) (closure B) :=
    C.disjoint_closure_projectiveClosedCoreLift_exterior S a ha
  have hAsub : A ⊆ Kᶜ := connectedComponentIn_subset _ _
  have hclAsub : closure A ⊆ (interior K)ᶜ := by
    simpa only [closure_compl] using closure_mono hAsub
  let δ := C.boundary_neck.epsilon⁻¹
  have hδ : 0 < δ := inv_pos.mpr C.boundary_neck.epsilon_pos
  have hzero (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ e.source := by
    rw [hes]
    exact ⟨mem_univ _, neg_lt_zero.mpr hδ, hδ⟩
  have hzero_cl (q : UnitTwoSphere) : e (q, 0) ∈ closure A :=
    frontier_subset_closure (hfront.symm.subset (mem_range_self q))
  have heA : Kᶜ ∩ e.target ⊆ A := by
    have hc := C.isConnected_projective_boundary_collar_exterior S e hes hmem hlift
    apply hc.isPreconnected.subset_left_of_subset_union hA hB hdis
      (fun y hy => hcover.symm.subset hy.1)
    let q := Poincare.Topology.standardSpherePole 0
    obtain ⟨y, hyt, hyA⟩ := mem_closure_iff.mp (hzero_cl q)
      e.target e.open_target (e.map_source (hzero q))
    exact ⟨y, ⟨hAsub hyA, hyt⟩, hyA⟩
  have htarget (y : UnitThreeSphere) (hy : y ∈ e.target) :
      Quotient.mk' y ≠ C.puncture := by
    simpa only [e.right_inv hy] using hmem _ (e.map_target hy)
  have hpos
      (hin : e '' (univ ×ˢ Ioo (-δ) 0) ⊆ interior K)
      (hout : e '' (univ ×ˢ Ioo 0 δ) ⊆ Kᶜ) :
      ∀ y ∈ e.target, y ∈ closure A ↔ 0 ≤ (e.symm y).2 := by
    intro y hy
    have hz := hes ▸ e.map_target hy
    constructor
    · intro hcl
      by_contra hn
      have ht : (e.symm y).2 < 0 := lt_of_not_ge hn
      exact hclAsub hcl (hin ⟨e.symm y, ⟨mem_univ _, hz.2.1, ht⟩, e.right_inv hy⟩)
    · intro ht
      rcases lt_or_eq_of_le ht with ht | ht
      · apply subset_closure
        exact heA ⟨hout ⟨e.symm y, ⟨mem_univ _, ht, hz.2.2⟩, e.right_inv hy⟩, hy⟩
      · have hz0 : e.symm y = ((e.symm y).1, 0) := Prod.ext rfl ht.symm
        have h := hzero_cl (e.symm y).1
        rw [← hz0, e.right_inv hy] at h
        exact h
  have hneg
      (hin : e '' (univ ×ˢ Ioo 0 δ) ⊆ interior K)
      (hout : e '' (univ ×ˢ Ioo (-δ) 0) ⊆ Kᶜ) :
      ∀ y ∈ e.target, y ∈ closure A ↔ (e.symm y).2 ≤ 0 := by
    intro y hy
    have hz := hes ▸ e.map_target hy
    constructor
    · intro hcl
      by_contra hn
      have ht : 0 < (e.symm y).2 := lt_of_not_ge hn
      exact hclAsub hcl (hin ⟨e.symm y, ⟨mem_univ _, ht, hz.2.2⟩, e.right_inv hy⟩)
    · intro ht
      rcases lt_or_eq_of_le ht with ht | ht
      · apply subset_closure
        exact heA ⟨hout ⟨e.symm y, ⟨mem_univ _, hz.2.1, ht⟩, e.right_inv hy⟩, hy⟩
      · have hz0 : e.symm y = ((e.symm y).1, 0) := Prod.ext rfl ht
        have h := hzero_cl (e.symm y).1
        rw [← hz0, e.right_inv hy] at h
        exact h
  rcases C.projective_boundary_collar_sides S e hes hmem hlift with ⟨hin, hout⟩ | ⟨hin, hout⟩
  · refine ⟨δ, hδ, e, hes, he, hei, htarget, hfront, hpos hin hout,
      1, Or.inl rfl, ?_⟩
    intro z hz
    simpa only [one_mul, Prod.mk.eta] using hlift z hz
  · let J : Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞ := {
      toEquiv := (Equiv.refl UnitTwoSphere).prodCongr (Equiv.neg ℝ)
      contMDiff_toFun := contMDiff_fst.prodMk contMDiff_snd.neg
      contMDiff_invFun := contMDiff_fst.prodMk contMDiff_snd.neg }
    let d := J.toHomeomorph.toOpenPartialHomeomorph.trans e
    have hds : d.source = univ ×ˢ Ioo (-δ) δ := by
      ext z
      change (z ∈ univ ∧ (z.1, -z.2) ∈ e.source) ↔ _
      rw [hes]
      change (True ∧ (True ∧ (-δ < -z.2 ∧ -z.2 < δ))) ↔
        (True ∧ (-δ < z.2 ∧ z.2 < δ))
      simp only [true_and]
      constructor <;> rintro ⟨hl, hr⟩ <;> constructor <;> linarith
    have hdt : d.target = e.target := by simp [d]
    refine ⟨δ, hδ, d, hds, ?_, ?_, ?_, ?_, ?_, -1, Or.inr rfl, ?_⟩
    · exact he.comp J.contMDiff.contMDiffOn inter_subset_right
    · exact J.symm.contMDiff.comp_contMDiffOn (hei.mono inter_subset_left)
    · intro y hy
      exact htarget y (hdt ▸ hy)
    · have hd0 (q : UnitTwoSphere) : d (q, 0) = e (q, 0) := by
        change e (q, -(0 : ℝ)) = e (q, 0)
        rw [neg_zero]
      simpa only [hd0] using hfront
    · intro y hy
      change y ∈ closure A ↔ 0 ≤ -(e.symm y).2
      rw [neg_nonneg]
      exact hneg hin hout y (hdt ▸ hy)
    · intro z hz
      change S.cover (e (z.1, -z.2)) =
        C.boundary_neck.coordinate_map (z.1, (-1 : ℝ) * z.2)
      simpa only [neg_one_mul] using hlift (z.1, -z.2) hz.2

end PoincareConjecture.CapCertificate
