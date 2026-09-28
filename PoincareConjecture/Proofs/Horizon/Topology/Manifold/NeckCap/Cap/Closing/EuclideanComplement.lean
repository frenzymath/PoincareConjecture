import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.EuclideanDecomposition
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.CollaredDomain
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Neighborhood
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.Embedding
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothDomain.Embedding
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothDomain.FromEmbedding
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Separation.Connected













set_option autoImplicit false

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.CapCertificate

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)


variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}





theorem exists_two_cap_euclidean_complementary_balls (C D : CapCertificate g)
    (hC : C.model_kind = .euclidean) (hD : D.model_kind = .euclidean)
    (hcompact : IsCompact (C.carrier ∪ D.carrier)) :
    ∃ b d : OpenPartialHomeomorph E3 M,
      b.source = univ ∧ b.target = D.carrier ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target ∧
      Metric.closedBall 0 1 ⊆ d.source ∧
      d.target ⊆ C.carrier ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ d d.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ d.symm d.target ∧
      d '' Metric.closedBall 0 1 = (C.carrier ∪ D.carrier) \ b '' Metric.ball 0 1 ∧
      d '' Metric.ball 0 1 = (C.carrier ∪ D.carrier) \ b '' Metric.closedBall 0 1 ∧
      d '' Metric.sphere 0 1 = b '' Metric.sphere 0 1 ∧
      b '' Metric.closedBall 0 1 ∪ d '' Metric.closedBall 0 1 = C.carrier ∪ D.carrier ∧
      b '' Metric.closedBall 0 1 ∩ d '' Metric.closedBall 0 1 = b '' Metric.sphere 0 1 ∧
      ∃ c : OpenPartialHomeomorph RoundCylinderSpace M,
        c.source = univ ∧
        ContMDiffOn CylModel (𝓡 3) ∞ c c.source ∧
        ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target ∧
        (∀ z : RoundCylinderSpace, c z = b (Real.exp z.2 • (z.1 : E3))) ∧
        c '' (univ ×ˢ ({0} : Set ℝ)) = b '' Metric.sphere 0 1 ∧
        ∃ ε : ℝ, 0 < ε ∧
          c '' (univ ×ˢ Ioo (-ε) ε) ⊆ b.target ∩ d.target ∧
          c '' (univ ×ˢ Ioo (-ε) 0) ⊆ b '' Metric.ball 0 1 ∧
          c '' (univ ×ˢ Ioo 0 ε) ⊆ d '' Metric.ball 0 1 := by
  obtain ⟨b, hbs, hbt, hb, hbi, _, _, hLc, hLC, hcover, hinter,
    _, _, _, hLi, hLcl, hLf, c, hcs, hc, hci, hformula, hczero, δ, hδ,
    hcollar, hnegative, hpositive⟩ :=
    C.exists_two_cap_euclidean_ball_decomposition D hD hcompact
  obtain ⟨e, hes, het, he, hei⟩ := C.exists_euclidean_coordinates hC
  let L := (C.carrier ∪ D.carrier) \ b '' Metric.ball 0 1
  let K := e '' L
  have hLs : L ⊆ e.source := hes.symm ▸ hLC
  have hKc : IsCompact K := hLc.image_of_continuousOn (e.continuousOn.mono hLs)
  have himage : e.IsImage L K := e.isImage_image_of_subset_source hLs
  have hKi : interior K = e '' interior L := by
    have h := himage.interior.image_eq
    rw [inter_eq_right.mpr (interior_subset.trans hLs), het, univ_inter] at h
    exact h.symm
  have hLregular : closure (interior L) = L := by
    rw [hLi]
    exact hLcl
  have hKregular : closure (interior K) = K := by
    rw [hKi]
    obtain ⟨_, _, hclosure, _⟩ := e.image_region_of_isCompact_closure
      isOpen_interior (hLregular.symm ▸ hLc) (hLregular.symm ▸ hLs)
    simpa only [hLregular] using hclosure
  have hKf : frontier K = e '' frontier L := by
    have h := himage.frontier.image_eq
    rw [inter_eq_right.mpr (hLc.isClosed.frontier_subset.trans hLs), het, univ_inter] at h
    exact h.symm
  let j := c.trans e
  have hj : ContMDiffOn CylModel (𝓡 3) ∞ j j.source :=
    he.comp (hc.mono inter_subset_left) inter_subset_right
  have hji : ContMDiffOn (𝓡 3) CylModel ∞ j.symm j.target :=
    hci.comp (hei.mono inter_subset_left) inter_subset_right
  have hjs : univ ×ˢ Ioo (-δ) δ ⊆ j.source := by
    intro z hz
    refine ⟨?_, hes.symm ▸ (hcollar ⟨z, hz, rfl⟩).1⟩
    change z ∈ c.source
    rw [hcs]
    exact mem_univ _
  have hfront : frontier K = range (fun q : UnitTwoSphere => j (q, 0)) := by
    rw [hKf, hLf, ← hczero]
    ext x
    constructor
    · rintro ⟨_, ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩, rfl⟩
      have ht0 : t = 0 := ht
      subst t
      exact ⟨q, rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨c (q, 0), ⟨(q, 0), ⟨mem_univ _, rfl⟩, rfl⟩, rfl⟩
  have hbinj : Function.Injective b := (b.isOpenEmbedding hbs).injective
  have hbD (x : E3) : b x ∈ D.carrier := hbt ▸ b.map_source (hbs.symm ▸ mem_univ _)
  have hbball (x : E3) : b x ∈ b '' Metric.ball 0 1 ↔ ‖x‖ < 1 := by
    constructor
    · rintro ⟨y, hy, heq⟩
      exact mem_ball_zero_iff.mp (hbinj heq ▸ hy)
    · intro hx
      exact ⟨x, mem_ball_zero_iff.mpr hx, rfl⟩
  have hcL (z : RoundCylinderSpace) : c z ∈ L ↔ 0 ≤ z.2 := by
    change (c z ∈ C.carrier ∪ D.carrier ∧ ¬ c z ∈ b '' Metric.ball 0 1) ↔ _
    rw [hformula, hbball]
    have hnorm : ‖Real.exp z.2 • (z.1 : E3)‖ = Real.exp z.2 := by
      simp [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [hnorm, Real.exp_lt_one_iff]
    simp only [show b (Real.exp z.2 • (z.1 : E3)) ∈ C.carrier ∪ D.carrier from
      Or.inr (hbD _), true_and, not_lt]
  have hside (y : E3) (hy : y ∈ j.target) : y ∈ K ↔ 0 ≤ (j.symm y).2 := by
    rw [← himage.symm_apply_mem_iff hy.1]
    have h := hcL (c.symm (e.symm y))
    rw [c.right_inv hy.2] at h
    exact h
  obtain ⟨f, hfs, hft, hf, hfi, hfK⟩ :=
    Poincare.Manifold.Schoenflies.ball_neighborhood_of_compact_collar_side
      hKc hKregular j hj hji hδ hjs hfront hside
  let d := f.trans e.symm
  have hds : Metric.closedBall (0 : E3) 1 ⊆ d.source := by
    intro x hx
    refine ⟨hfs hx, ?_⟩
    change f x ∈ e.target
    rw [het]
    exact mem_univ _
  have hdt : d.target ⊆ C.carrier := fun x hx => hes ▸ hx.1
  have hd : ContMDiffOn (𝓡 3) (𝓡 3) ∞ d d.source :=
    hei.comp (hf.mono inter_subset_left) inter_subset_right
  have hdi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ d.symm d.target :=
    hfi.comp (he.mono inter_subset_left) inter_subset_right
  have hdL : d '' Metric.closedBall 0 1 = L := by
    change (e.symm ∘ f) '' Metric.closedBall 0 1 = L
    rw [image_comp, hfK]
    exact e.toPartialEquiv.symm_image_image_of_subset_source hLs
  have hdiL : d '' Metric.ball 0 1 =
      (C.carrier ∪ D.carrier) \ b '' Metric.closedBall 0 1 := by
    rw [d.image_ball_eq_interior hds hdL]
    exact hLi
  have hdfL : d '' Metric.sphere 0 1 = b '' Metric.sphere 0 1 := by
    rw [d.image_sphere_eq_frontier hds hdL]
    exact hLf
  have hcc : Continuous c := continuousOn_univ.mp (hcs ▸ c.continuousOn)
  let V : Opens RoundCylinderSpace :=
    ⟨c ⁻¹' d.target ∩ (univ ×ˢ Ioo (-δ) δ),
      (d.open_target.preimage hcc).inter (isOpen_univ.prod isOpen_Ioo)⟩
  have hzeroV (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ V := by
    refine ⟨?_, mem_univ _, neg_lt_zero.mpr hδ, hδ⟩
    have hz : c (q, 0) ∈ d '' Metric.sphere 0 1 := by
      rw [hdfL, ← hczero]
      exact mem_image_of_mem c ⟨mem_univ _, rfl⟩
    obtain ⟨x, hx, hxeq⟩ := hz
    change c (q, 0) ∈ d.target
    exact hxeq ▸ d.map_source (hds (Metric.sphere_subset_closedBall hx))
  obtain ⟨ε, hε, hεV⟩ := CylinderGluing.exists_cylinder_collar V hzeroV
  refine ⟨b, d, hbs, hbt, hb, hbi, hds, hdt, hd, hdi, hdL, hdiL, hdfL,
    ?_, ?_, c, hcs, hc, hci, hformula, hczero, ε, hε, ?_, ?_, ?_⟩
  · rw [hdL]
    exact hcover
  · rw [hdL]
    exact hinter
  · rintro _ ⟨z, hz, rfl⟩
    have hzV := hεV z (abs_lt.mpr hz.2)
    exact ⟨hbt.symm ▸ (hcollar ⟨z, hzV.2, rfl⟩).2, hzV.1⟩
  · rintro _ ⟨z, hz, rfl⟩
    have hzV := hεV z (abs_lt.mpr ⟨hz.2.1, hz.2.2.trans hε⟩)
    exact hnegative ⟨z, ⟨mem_univ _, hzV.2.2.1, hz.2.2⟩, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    have hzV := hεV z (abs_lt.mpr ⟨(neg_lt_zero.mpr hε).trans hz.2.1, hz.2.2⟩)
    rw [hdiL]
    exact hpositive ⟨z, ⟨mem_univ _, hz.2.1, hzV.2.2.2⟩, rfl⟩

end PoincareConjecture.CapCertificate
