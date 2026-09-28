import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Projective.CoreNeighborhood
import PoincareConjecture.Proofs.Horizon.Topology.Maps.OpenPartialHomeomorph.Compact













noncomputable section
set_option autoImplicit false

open Set Topology IsManifold
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



theorem exists_projective_exterior_ball_neighborhood
    (a : UnitThreeSphere) (ha : Quotient.mk' a = C.puncture) :
    let A := connectedComponentIn (C.projectiveClosedCoreLift S)ᶜ a
    ∃ b : OpenPartialHomeomorph E3 UnitThreeSphere,
      Metric.closedBall 0 1 ⊆ b.source ∧ closure A ⊆ b.target ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target ∧
      b '' Metric.closedBall 0 1 = closure A ∧
      b '' Metric.ball 0 1 = A ∧ b '' Metric.sphere 0 1 = frontier A := by
  let A := connectedComponentIn (C.projectiveClosedCoreLift S)ᶜ a
  obtain ⟨hA, _, _, _, haA, _⟩ := C.projectiveClosedCoreLift_exterior_components S a ha
  obtain ⟨δ, hδ, e, hes, he, hei, hmem, hfront, hside, _⟩ :=
    C.exists_oriented_projective_exterior_collar S a ha
  have hzero (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ e.source := by
    rw [hes]
    exact ⟨mem_univ _, neg_lt_zero.mpr hδ, hδ⟩
  have hiA : interior (closure A) = A := by
    apply Subset.antisymm _ hA.subset_interior_closure
    intro y hy
    by_contra hyA
    have hyf : y ∈ frontier A := by
      rw [hA.frontier_eq]
      exact ⟨interior_subset hy, hyA⟩
    obtain ⟨q, rfl⟩ := hfront.subset hyf
    have himage : e.symm.IsImage (closure A) (univ ×ˢ Ici (0 : ℝ)) := by
      intro z hz
      simpa only [mem_prod, mem_univ, true_and, mem_Ici] using (hside z hz).symm
    have hpos := (himage.interior (e.map_source (hzero q))).mpr hy
    rw [e.left_inv (hzero q)] at hpos
    simp only [interior_prod_eq, interior_univ, interior_Ici, mem_prod,
      mem_univ, true_and, mem_Ioi, lt_self_iff_false] at hpos
  have hLf : frontier (closure A) = frontier A := by
    rw [isClosed_closure.frontier_eq, hiA, hA.frontier_eq]
  have hLc : IsCompact (closure A) := isClosed_closure.isCompact
  have hdis := C.disjoint_closure_projectiveClosedCoreLift_exterior S a ha
  have hneg : -a ∉ closure A := by
    intro h
    exact Set.disjoint_left.mp hdis h (subset_closure (mem_image_of_mem Neg.neg haA))
  let p := SphereCharts.threeSphereStereographic (-a)
  have hps : p.source = {-a}ᶜ := SphereCharts.threeSphereStereographic_source _
  have hpt : p.target = univ := SphereCharts.threeSphereStereographic_target _
  have hp := contMDiffOn_of_mem_maximalAtlas
    (SphereCharts.threeSphereStereographic_mem_maximalAtlas (-a))
  have hpi := contMDiffOn_symm_of_mem_maximalAtlas
    (SphereCharts.threeSphereStereographic_mem_maximalAtlas (-a))
  have hLs : closure A ⊆ p.source := by
    intro y hy
    rw [hps]
    intro heq
    exact hneg ((mem_singleton_iff.mp heq) ▸ hy)
  have hnq : Quotient.mk' (-a) = C.puncture := by
    exact (Quotient.sound (show realProjectiveThreeSetoid (-a) a from Or.inr rfl)).trans ha
  have hetp : e.target ⊆ p.source := by
    intro y hy
    rw [hps]
    intro heq
    exact hmem y hy ((mem_singleton_iff.mp heq).symm ▸ hnq)
  let K := p '' closure A
  have hKc : IsCompact K := hLc.image_of_continuousOn (p.continuousOn.mono hLs)
  have himage : p.IsImage (closure A) K := p.isImage_image_of_subset_source hLs
  have hKi : interior K = p '' A := by
    have h := himage.interior.image_eq
    rw [hiA, inter_eq_right.mpr (subset_closure.trans hLs), hpt, univ_inter] at h
    exact h.symm
  have hKregular : closure (interior K) = K := by
    rw [hKi]
    exact (p.image_region_of_isCompact_closure hA hLc hLs).2.2.1
  have hKf : frontier K = p '' frontier A := by
    have h := himage.frontier.image_eq
    rw [hLf, inter_eq_right.mpr (frontier_subset_closure.trans hLs), hpt, univ_inter] at h
    exact h.symm
  let c := e.trans p
  have hc : ContMDiffOn CylModel (𝓡 3) ∞ c c.source :=
    hp.comp (he.mono inter_subset_left) inter_subset_right
  have hci : ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target :=
    hei.comp (hpi.mono inter_subset_left) inter_subset_right
  have hcs : univ ×ˢ Ioo (-δ) δ ⊆ c.source := by
    intro z hz
    have hz' : z ∈ e.source := hes.symm ▸ hz
    exact ⟨hz', hetp (e.map_source hz')⟩
  have hcf : frontier K = range (fun q : UnitTwoSphere => c (q, 0)) := by
    rw [hKf, hfront, ← range_comp]
    rfl
  have hcsid (y : E3) (hy : y ∈ c.target) :
      y ∈ K ↔ 0 ≤ (c.symm y).2 := by
    rw [← himage.symm_apply_mem_iff hy.1]
    exact hside _ hy.2
  obtain ⟨f, hfs, _, hf, hfi, hfK⟩ :=
    Poincare.Manifold.Schoenflies.ball_neighborhood_of_compact_collar_side
      hKc hKregular c hc hci hδ hcs hcf hcsid
  let b := f.trans p.symm
  have hbs : Metric.closedBall (0 : E3) 1 ⊆ b.source := by
    intro x hx
    refine ⟨hfs hx, ?_⟩
    change f x ∈ p.target
    rw [hpt]
    exact mem_univ _
  have hb : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source :=
    hpi.comp (hf.mono inter_subset_left) inter_subset_right
  have hbi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target :=
    hfi.comp (hp.mono inter_subset_left) inter_subset_right
  have hbL : b '' Metric.closedBall 0 1 = closure A := by
    change (p.symm ∘ f) '' Metric.closedBall 0 1 = closure A
    rw [image_comp, hfK]
    exact p.toPartialEquiv.symm_image_image_of_subset_source hLs
  refine ⟨b, hbs, ?_, hb, hbi, hbL, ?_, ?_⟩
  · rw [← hbL]
    exact image_subset_iff.mpr (fun _ hx => b.map_source (hbs hx))
  · exact (b.image_ball_eq_interior hbs hbL).trans hiA
  · exact (b.image_sphere_eq_frontier hbs hbL).trans hLf





theorem exists_projective_exterior_antipodal_balls
    (a : UnitThreeSphere) (ha : Quotient.mk' a = C.puncture) :
    let K := C.projectiveClosedCoreLift S
    let A := connectedComponentIn Kᶜ a
    ∃ b d : OpenPartialHomeomorph E3 UnitThreeSphere,
      Metric.closedBall 0 1 ⊆ b.source ∧
      Metric.closedBall 0 1 ⊆ d.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ d d.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ d.symm d.target ∧
      (∀ x, d x = -b x) ∧
      b '' Metric.closedBall 0 1 = closure A ∧
      d '' Metric.closedBall 0 1 = closure (Neg.neg '' A) ∧
      b '' Metric.ball 0 1 = A ∧
      d '' Metric.ball 0 1 = Neg.neg '' A ∧
      Disjoint (b '' Metric.closedBall 0 1) (d '' Metric.closedBall 0 1) ∧
      b '' Metric.ball 0 1 ∪ d '' Metric.ball 0 1 = Kᶜ ∧
      b '' Metric.closedBall 0 1 ∪ d '' Metric.closedBall 0 1 = (interior K)ᶜ := by
  let K := C.projectiveClosedCoreLift S
  let A := connectedComponentIn Kᶜ a
  obtain ⟨b, hbs, _, hb, hbi, hbcl, hbopen, _⟩ :=
    C.exists_projective_exterior_ball_neighborhood S a ha
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
  let J : Diffeomorph (𝓡 3) (𝓡 3) UnitThreeSphere UnitThreeSphere ∞ := {
    toEquiv := Equiv.neg UnitThreeSphere
    contMDiff_toFun := contMDiff_neg_sphere
    contMDiff_invFun := contMDiff_neg_sphere }
  let d := b.trans J.toHomeomorph.toOpenPartialHomeomorph
  have hds : d.source = b.source := by simp [d]
  have hd : ContMDiffOn (𝓡 3) (𝓡 3) ∞ d d.source :=
    J.contMDiff.comp_contMDiffOn (hb.mono (hds ▸ Subset.rfl))
  have hdi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ d.symm d.target :=
    hbi.comp J.symm.contMDiff.contMDiffOn inter_subset_right
  have hdim (s : Set E3) : d '' s = Neg.neg '' (b '' s) := by
    change (Neg.neg ∘ b) '' s = _
    rw [image_comp]
  have hdcl : d '' Metric.closedBall 0 1 = closure (Neg.neg '' A) := by
    rw [hdim, hbcl]
    exact (Homeomorph.neg UnitThreeSphere).image_closure A
  have hdopen : d '' Metric.ball 0 1 = Neg.neg '' A := by
    rw [hdim, hbopen]
  obtain ⟨_, _, _, hcover, _, _⟩ := C.projectiveClosedCoreLift_exterior_components S a ha
  refine ⟨b, d, hbs, hds.symm ▸ hbs, hb, hbi, hd, hdi, fun _ => rfl,
    hbcl, hdcl, hbopen, hdopen, ?_, ?_, ?_⟩
  · rw [hbcl, hdcl]
    exact C.disjoint_closure_projectiveClosedCoreLift_exterior S a ha
  · rw [hbopen, hdopen]
    exact hcover
  · rw [hbcl, hdcl, ← closure_union, hcover, closure_compl]

end PoincareConjecture.CapCertificate
