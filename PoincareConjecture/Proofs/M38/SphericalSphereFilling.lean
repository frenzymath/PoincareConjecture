import PoincareConjecture.Proofs.M38.SphereCollarSides
import PoincareConjecture.Proofs.M38.CollaredChartFilling
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.SphereCharts.EmbeddedSphereCollar
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Sphere
import PoincareConjecture.Proofs.M38.SurgeryBallTopology
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothEmbedding.LocalDiffeomorph











set_option autoImplicit false

open Set IsManifold
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M38

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

private theorem fill_sphere_positive_collar_side
    (p : UnitThreeSphere) {A B : Set UnitThreeSphere}
    (hA : IsOpen A) (hB : IsOpen B) (hd : Disjoint A B) (hpA : p ∈ A)
    (c : OpenPartialHomeomorph RoundCylinderSpace UnitThreeSphere)
    {δ : ℝ} (hδ : 0 < δ) (hcs : c.source = univ ×ˢ Ioo (-δ) δ)
    (hct : c.target ⊆ {p}ᶜ)
    (hc : ContMDiffOn CylModel (𝓡 3) ∞ c c.source)
    (hci : ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target)
    (hfB : frontier B = range (fun z : UnitTwoSphere => c (z, 0)))
    (hn : c '' (univ ×ˢ Ioo (-δ) 0) ⊆ A)
    (hp : c '' (univ ×ˢ Ioo 0 δ) ⊆ B) :
    ∃ b : OpenPartialHomeomorph StandardCapSpace UnitThreeSphere,
      Metric.closedBall 0 1 ⊆ b.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target ∧
      b '' Metric.sphere 0 1 = range (fun z : UnitTwoSphere => c (z, 0)) ∧
      p ∉ b '' Metric.closedBall 0 1 := by
  obtain ⟨hi, hf, hside⟩ := sphere_collar_positive_closed_side hA hB hd c hδ hcs hfB hn hp
  have hcl : closure B ⊆ Aᶜ := closure_minimal (disjoint_right.mp hd) hA.isClosed_compl
  let e := PoincareConjecture.SphereCharts.threeSphereStereographic p
  have hes : e.source = {p}ᶜ := PoincareConjecture.SphereCharts.threeSphereStereographic_source p
  have hKs : closure B ⊆ e.source := by
    intro y hy
    rw [hes]
    intro heq
    exact hcl hy (mem_singleton_iff.mp heq ▸ hpA)
  obtain ⟨b, hbs, _, hb, hbi, hbK⟩ := exists_ballNeighborhood_in_coordinates e
    (contMDiffOn_of_mem_maximalAtlas
      (PoincareConjecture.SphereCharts.threeSphereStereographic_mem_maximalAtlas p))
    (contMDiffOn_symm_of_mem_maximalAtlas
      (PoincareConjecture.SphereCharts.threeSphereStereographic_mem_maximalAtlas p))
    isClosed_closure.isCompact hKs (by rw [hi]) c hc hci hδ hcs.superset
    (hct.trans hes.symm.subset) hf hside
  exact ⟨b, hbs, hb, hbi, (b.image_sphere_eq_frontier hbs hbK).trans hf,
    by rw [hbK]; exact fun hp => hcl hp hpA⟩




theorem exists_sphere_ballNeighborhood_avoiding_point
    (f : UnitTwoSphere → UnitThreeSphere)
    (hf : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (p : UnitThreeSphere) (hpf : p ∉ range f) :
    ∃ b : OpenPartialHomeomorph StandardCapSpace UnitThreeSphere,
      Metric.closedBall 0 1 ⊆ b.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target ∧
      b '' Metric.sphere 0 1 = range f ∧ p ∉ b '' Metric.closedBall 0 1 := by
  let : SimplyConnectedSpace UnitThreeSphere := Poincare.Topology.standardSphereSimplyConnected 1
  let : LocallyPathConnectedSpace UnitThreeSphere :=
    ChartedSpace.locallyPathConnectedSpace StandardCapSpace UnitThreeSphere
  obtain ⟨δ, hδ, c, hcs, hct, hc, hci, hcf⟩ :=
    PoincareConjecture.SphereCharts.exists_embeddedSphere_collar_avoiding_point f hf p hpf
  obtain ⟨A, B, hA, hB, _, _, hd, hcover, hfA, hfB, hn, hp⟩ :=
    exists_sphere_collar_sides c hδ hcs
  have hS : range (fun z : UnitTwoSphere => c (z, 0)) = range f := by simp only [hcf]
  have hpAB : p ∈ A ∪ B := by rw [hcover, hS]; exact hpf
  rcases hpAB with hpA | hpB
  · obtain ⟨b, hbs, hb, hbi, hbS, hbp⟩ :=
      fill_sphere_positive_collar_side p hA hB hd hpA c hδ hcs hct hc hci hfB hn hp
    exact ⟨b, hbs, hb, hbi, hbS.trans hS, hbp⟩
  · let J := projectiveCollarReflection
    let d := J.toHomeomorph.toOpenPartialHomeomorph.trans c
    have hds : d.source = univ ×ˢ Ioo (-δ) δ := by
      ext z
      change (z ∈ univ ∧ (z.1, -z.2) ∈ c.source) ↔ _
      rw [hcs]
      change (True ∧ (True ∧ (-δ < -z.2 ∧ -z.2 < δ))) ↔
        (True ∧ (-δ < z.2 ∧ z.2 < δ))
      simp only [true_and]
      constructor <;> rintro ⟨hl, hr⟩ <;> constructor <;> linarith
    have hdt : d.target = c.target := by simp [d]
    have hd0 (z : UnitTwoSphere) : d (z, 0) = c (z, 0) := by
      change c (z, -(0 : ℝ)) = c (z, 0)
      rw [neg_zero]
    have hdS : range (fun z : UnitTwoSphere => d (z, 0)) = range f := by
      simp only [hd0, hcf]
    obtain ⟨b, hbs, hb, hbi, hbS, hbp⟩ :=
      fill_sphere_positive_collar_side p hB hA hd.symm hpB d hδ hds (hdt ▸ hct)
        (hc.comp J.contMDiff.contMDiffOn inter_subset_right)
        (J.symm.contMDiff.comp_contMDiffOn (hci.mono inter_subset_left))
        (by simpa only [hd0] using hfA)
        (by
          rintro _ ⟨z, hz, rfl⟩
          exact hp ⟨(z.1, -z.2),
            ⟨mem_univ _, by linarith [hz.2.2], by linarith [hz.2.1]⟩, rfl⟩)
        (by
          rintro _ ⟨z, hz, rfl⟩
          exact hn ⟨(z.1, -z.2),
            ⟨mem_univ _, by linarith [hz.2.2], by linarith [hz.2.1]⟩, rfl⟩)
    exact ⟨b, hbs, hb, hbi, hbS.trans hdS, hbp⟩



theorem exists_surgerySphereBall_avoiding_point
    (f : UnitTwoSphere → sphereCarrier.{u}.carrier)
    (hf : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (p : sphereCarrier.{u}.carrier) (hpf : p ∉ range f) :
    ∃ B : SurgeryBallEmbedding sphereCarrier.{u},
      frontier B.closedBall = range f ∧ p ∉ B.closedBall := by
  let d : Diffeomorph (𝓡 3) (𝓡 3) UnitThreeSphere sphereCarrier.{u}.carrier ∞ := {
    toEquiv := (Homeomorph.ulift : sphereCarrier.{u}.carrier ≃ₜ UnitThreeSphere).symm.toEquiv
    contMDiff_toFun := threeManifold_up_contMDiff UnitThreeSphere
    contMDiff_invFun := threeManifold_down_contMDiff UnitThreeSphere }
  let F := d.symm ∘ f
  have hF : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ F :=
    hf.comp_localDiffeomorph d.symm.isLocalDiffeomorph
      (d.symm.injective.comp hf.isEmbedding.injective)
  have hpF : d.symm p ∉ range F := by
    rintro ⟨z, hz⟩
    exact hpf ⟨z, d.symm.injective hz⟩
  obtain ⟨b, hbs, hb, hbi, hbf, hbp⟩ :=
    exists_sphere_ballNeighborhood_avoiding_point F hF (d.symm p) hpF
  let c := b.trans d.toHomeomorph.toOpenPartialHomeomorph
  have hcs : Metric.closedBall (0 : StandardCapSpace) 1 ⊆ c.source :=
    fun x hx => ⟨hbs hx, mem_univ _⟩
  have hc : ContMDiffOn (𝓡 3) (𝓡 3) ∞ c c.source :=
    d.contMDiff.comp_contMDiffOn (hb.mono inter_subset_left)
  have hci : ContMDiffOn (𝓡 3) (𝓡 3) ∞ c.symm c.target :=
    hbi.comp d.symm.contMDiff.contMDiffOn inter_subset_right
  obtain ⟨_, B, _, _, hBc, _, _⟩ := exists_surgeryBall_of_ballNeighborhood c hc hci hcs
  refine ⟨B, ?_, ?_⟩
  · rw [← c.image_sphere_eq_frontier hcs hBc.symm]
    change (d ∘ b) '' Metric.sphere 0 1 = range f
    rw [image_comp, hbf, ← range_comp]
    have hcomp : d ∘ F = f := by
      funext z
      exact d.apply_symm_apply (f z)
    rw [hcomp]
  · rw [hBc]
    rintro ⟨x, hx, hxp⟩
    apply hbp
    refine ⟨x, hx, ?_⟩
    have h := congrArg d.symm hxp
    change d.symm (d (b x)) = d.symm p at h
    simpa only [Diffeomorph.symm_apply_apply] using h

end PoincareConjecture.M38
