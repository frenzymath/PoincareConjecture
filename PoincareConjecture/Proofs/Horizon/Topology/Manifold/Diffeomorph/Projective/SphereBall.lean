import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.SphereCharts.EmbeddedSphereCollar
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Separation.Antipodal
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Separation.Components
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Coordinates
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Sphere

noncomputable section
set_option autoImplicit false

open Set PoincareConjecture IsManifold
open scoped Manifold ContDiff Topology

namespace Poincare.Projective

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

private theorem collar_sides
    (e : OpenPartialHomeomorph RoundCylinderSpace UnitThreeSphere)
    {δ : ℝ} (hδ : 0 < δ) (hes : e.source = univ ×ˢ Ioo (-δ) δ) :
    let S := range (fun q : UnitTwoSphere => e (q, 0))
    ∃ A B : Set UnitThreeSphere,
      IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
      Disjoint A B ∧ A ∪ B = Sᶜ ∧ frontier A = S ∧ frontier B = S ∧
      e '' (univ ×ˢ Ioo (-δ) 0) ⊆ A ∧
      e '' (univ ×ˢ Ioo 0 δ) ⊆ B := by
  let : SimplyConnectedSpace UnitThreeSphere := Poincare.Topology.standardSphereSimplyConnected 1
  let : LocallyPathConnectedSpace UnitThreeSphere :=
    ChartedSpace.locallyPathConnectedSpace E3 UnitThreeSphere
  let : ConnectedSpace UnitTwoSphere := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (E := E3) (by rw [← Module.finrank_eq_rank]; norm_num)
      0 zero_le_one)
  let j : (UnitTwoSphere × Ioo (-δ) δ) ≃ₜ e.target :=
    ((Homeomorph.Set.prod (univ : Set UnitTwoSphere) (Ioo (-δ) δ)).trans
      ((Homeomorph.Set.univ UnitTwoSphere).prodCongr (Homeomorph.refl _))).symm.trans
        ((Homeomorph.setCongr hes.symm).trans e.toHomeomorphSourceTarget)
  obtain ⟨A, B, hA, hB, hcA, hcB, hdis, hcover, hfA, hfB, hn, hp⟩ :=
    Poincare.Topology.exists_collar_complementary_regions hδ e.open_target j
  refine ⟨A, B, hA, hB, hcA, hcB, hdis, hcover, hfA, hfB, ?_, ?_⟩
  · rintro y ⟨z, hz, rfl⟩
    exact hn ⟨(z.1, ⟨z.2, hz.2.1, hz.2.2.trans hδ⟩), hz.2.2, rfl⟩
  · rintro y ⟨z, hz, rfl⟩
    exact hp ⟨(z.1, ⟨z.2, (neg_lt_zero.mpr hδ).trans hz.2.1, hz.2.2⟩), hz.2.1, rfl⟩

private theorem ball_of_positive_collar_side
    (a : UnitThreeSphere) {A B : Set UnitThreeSphere}
    (hA : IsOpen A) (hB : IsOpen B) (hdis : Disjoint A B) (haB : a ∈ B)
    (hanti : Disjoint (closure A) (Neg.neg '' closure A))
    (e : OpenPartialHomeomorph RoundCylinderSpace UnitThreeSphere)
    {δ : ℝ} (hδ : 0 < δ) (hes : e.source = univ ×ˢ Ioo (-δ) δ)
    (het : e.target ⊆ {a}ᶜ)
    (he : ContMDiffOn CylModel (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) CylModel ∞ e.symm e.target)
    (hfA : frontier A = range (fun q : UnitTwoSphere => e (q, 0)))
    (hn : e '' (univ ×ˢ Ioo (-δ) 0) ⊆ B)
    (hp : e '' (univ ×ˢ Ioo 0 δ) ⊆ A) :
    ∃ b : OpenPartialHomeomorph E3 UnitThreeSphere,
      Metric.closedBall 0 1 ⊆ b.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target ∧
      b '' Metric.sphere 0 1 = range (fun q : UnitTwoSphere => e (q, 0)) ∧
      Disjoint (b '' Metric.closedBall 0 1) (Neg.neg '' (b '' Metric.closedBall 0 1)) := by
  have hclB : closure A ⊆ Bᶜ :=
    closure_minimal (disjoint_left.mp hdis) hB.isClosed_compl
  have hzero (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ e.source :=
    hes.symm ▸ ⟨mem_univ _, neg_lt_zero.mpr hδ, hδ⟩
  have hside (y : UnitThreeSphere) (hy : y ∈ e.target) :
      y ∈ closure A ↔ 0 ≤ (e.symm y).2 := by
    have hz := hes ▸ e.map_target hy
    constructor
    · intro hcl
      by_contra ht
      exact hclB hcl (hn ⟨e.symm y,
        ⟨mem_univ _, hz.2.1, lt_of_not_ge ht⟩, e.right_inv hy⟩)
    · intro ht
      rcases lt_or_eq_of_le ht with ht | ht
      · exact subset_closure (hp ⟨e.symm y,
          ⟨mem_univ _, ht, hz.2.2⟩, e.right_inv hy⟩)
      · have hz0 : e.symm y = ((e.symm y).1, 0) := Prod.ext rfl ht.symm
        have hf : e ((e.symm y).1, 0) ∈ frontier A :=
          hfA.symm ▸ mem_range_self _
        rw [← hz0, e.right_inv hy] at hf
        exact frontier_subset_closure hf
  have hiA : interior (closure A) = A := by
    apply Subset.antisymm _ hA.subset_interior_closure
    intro y hy
    by_contra hyA
    have hyf : y ∈ frontier A := hA.frontier_eq.symm ▸ ⟨interior_subset hy, hyA⟩
    obtain ⟨q, rfl⟩ := hfA.subset hyf
    have himage : e.symm.IsImage (closure A) (univ ×ˢ Ici (0 : ℝ)) := by
      intro z hz
      simpa only [mem_prod, mem_univ, true_and, mem_Ici] using (hside z hz).symm
    have hpos := (himage.interior (e.map_source (hzero q))).mpr hy
    rw [e.left_inv (hzero q)] at hpos
    simp only [interior_prod_eq, interior_univ, interior_Ici, mem_prod,
      mem_univ, true_and, mem_Ioi, lt_self_iff_false] at hpos
  have hfront : frontier (closure A) = range (fun q : UnitTwoSphere => e (q, 0)) := by
    rw [isClosed_closure.frontier_eq, hiA, ← hA.frontier_eq, hfA]
  let p := SphereCharts.threeSphereStereographic a
  have hps : p.source = {a}ᶜ := SphereCharts.threeSphereStereographic_source a
  have hKs : closure A ⊆ p.source := by
    intro y hy
    rw [hps]
    intro heq
    exact hclB hy (mem_singleton_iff.mp heq ▸ haB)
  obtain ⟨b, hbs, _, hb, hbi, hbK⟩ :=
    Poincare.Manifold.Schoenflies.ball_neighborhood_in_coordinates p
      (SphereCharts.threeSphereStereographic_target a)
      (contMDiffOn_of_mem_maximalAtlas (SphereCharts.threeSphereStereographic_mem_maximalAtlas a))
      (contMDiffOn_symm_of_mem_maximalAtlas (SphereCharts.threeSphereStereographic_mem_maximalAtlas a))
      isClosed_closure.isCompact hKs (by rw [hiA]) e he hei hδ hes.superset
      (het.trans hps.symm.subset) hfront hside
  refine ⟨b, hbs, hb, hbi, (b.image_sphere_eq_frontier hbs hbK).trans hfront, ?_⟩
  simpa only [hbK] using hanti

theorem exists_antipodal_disjoint_sphere_ball
    (F : UnitTwoSphere → UnitThreeSphere)
    (hF : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ F)
    (hdis : Disjoint (range F) (Neg.neg '' range F)) :
    ∃ b : OpenPartialHomeomorph E3 UnitThreeSphere,
      Metric.closedBall 0 1 ⊆ b.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target ∧
      b '' Metric.sphere 0 1 = range F ∧
      Disjoint (b '' Metric.closedBall 0 1) (Neg.neg '' (b '' Metric.closedBall 0 1)) := by
  let : ConnectedSpace UnitTwoSphere := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (E := E3) (by rw [← Module.finrank_eq_rank]; norm_num)
      0 zero_le_one)
  let q₀ : UnitTwoSphere := Classical.choice inferInstance
  let a : UnitThreeSphere := -F q₀
  have ha : a ∈ Neg.neg '' range F := ⟨F q₀, mem_range_self q₀, rfl⟩
  have haF : a ∉ range F := fun h => disjoint_left.mp hdis h ha
  obtain ⟨δ, hδ, e, hes, het, he, hei, heF⟩ :=
    SphereCharts.exists_embeddedSphere_collar_avoiding_point F hF a haF
  obtain ⟨A, B, hA, hB, hcA, hcB, hAB, hcover, hfA, hfB, hn, hp⟩ :=
    collar_sides e hδ hes
  have heS : range (fun q : UnitTwoSphere => e (q, 0)) = range F := by
    simp only [heF]
  rw [heS] at hcover hfA hfB
  rcases Poincare.Topology.exists_disjoint_involutive_side
      (Homeomorph.neg UnitThreeSphere) neg_neg hA hB hcA hcB
      (isConnected_range hF.contMDiff.continuous) hAB hcover hfA hfB hdis with
    ⟨hanti, hpaired⟩ | ⟨hanti, hpaired⟩
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
    have hdF (q : UnitTwoSphere) : d (q, 0) = F q := by
      change e (q, -(0 : ℝ)) = F q
      rw [neg_zero, heF]
    have hdS : range (fun q : UnitTwoSphere => d (q, 0)) = range F := by
      simp only [hdF]
    obtain ⟨b, hbs, hb, hbi, hbS, hbdis⟩ := ball_of_positive_collar_side
      a hA hB hAB (hpaired ha) hanti d hδ hds (hdt ▸ het)
      (he.comp J.contMDiff.contMDiffOn inter_subset_right)
      (J.symm.contMDiff.comp_contMDiffOn (hei.mono inter_subset_left))
      (hfA.trans hdS.symm) (by
        rintro y ⟨z, hz, rfl⟩
        exact hp ⟨(z.1, -z.2), ⟨mem_univ _, by linarith [hz.2.2], by linarith [hz.2.1]⟩, rfl⟩)
      (by
        rintro y ⟨z, hz, rfl⟩
        exact hn ⟨(z.1, -z.2), ⟨mem_univ _, by linarith [hz.2.2], by linarith [hz.2.1]⟩, rfl⟩)
    exact ⟨b, hbs, hb, hbi, hbS.trans hdS, hbdis⟩
  · obtain ⟨b, hbs, hb, hbi, hbS, hbdis⟩ := ball_of_positive_collar_side
      a hB hA hAB.symm (hpaired ha) hanti e hδ hes het he hei
      (hfB.trans heS.symm) hn hp
    exact ⟨b, hbs, hb, hbi, hbS.trans heS, hbdis⟩

end Poincare.Projective
