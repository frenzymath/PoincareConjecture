import PoincareConjecture.Proofs.M25.Topology3D.Space3.CompactDiscTopology
import PoincareConjecture.Proofs.M25.Topology3D.Space3.RoundSphereDisc












set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

attribute [local instance] space3_stereographic_dimension



theorem exists_source_disc_complement (e : OpenPartialHomeomorph E2 UnitTwoSphere)
    (he : closedBall 0 1 ⊆ e.source)
    (G : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞)
    (v : UnitTwoSphere) {r : ℝ} (hr : 0 < r)
    (hG : G '' (e '' closedBall 0 1) = (stereographic' 2 v).symm '' closedBall 0 r) :
    ∃ f : OpenPartialHomeomorph E2 UnitTwoSphere,
      f.source = univ ∧
      ContMDiff 𝓘(ℝ, E2) (𝓡 2) ∞ f ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ f.symm f.target ∧
      (e '' closedBall 0 1) ∪ (f '' closedBall 0 1) = univ ∧
      (e '' closedBall 0 1) ∩ (f '' closedBall 0 1) = e '' sphere 0 1 ∧
      f '' sphere 0 1 = e '' sphere 0 1 ∧
      Disjoint (e '' ball 0 1) (f '' ball 0 1) ∧
      (e '' ball 0 1) ∪ (f '' ball 0 1) = (e '' sphere 0 1)ᶜ := by
  have hR : 0 < 4 / r := div_pos (by norm_num) hr
  generalize hd : roundSphereDiscChart (-v) (4 / r) hR = d
  have hds : d.source = univ := by
    rw [← hd]
    exact roundSphereDiscChart_source _ _ _
  have hdm : ContMDiff 𝓘(ℝ, E2) (𝓡 2) ∞ d := by
    rw [← hd]
    exact roundSphereDiscChart_contMDiff _ _ _
  have hdi : ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ d.symm d.target := by
    rw [← hd]
    exact roundSphereDiscChart_symm_contMDiffOn _ _ _
  let f := d.transHomeomorph G.symm.toHomeomorph
  have hfs : f.source = univ := by
    exact hds
  have hfc : closedBall 0 1 ⊆ f.source := by rw [hfs]; exact subset_univ _
  have hfsm : ContMDiff 𝓘(ℝ, E2) (𝓡 2) ∞ f := by
    change ContMDiff 𝓘(ℝ, E2) (𝓡 2) ∞ (fun x => G.symm (d x))
    exact G.contMDiff_invFun.comp hdm
  have hfsi : ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ f.symm f.target := by
    change ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ (fun y => d.symm (G y)) (G ⁻¹' d.target)
    exact hdi.comp G.contMDiff_toFun.contMDiffOn (fun _ hy => hy)
  have hclosed : G '' (f '' closedBall 0 1) =
      (stereographic' 2 (-v)).symm '' closedBall 0 (4 / r) := by
    calc
      _ = d '' closedBall 0 1 := by
        simp only [image_image]
        congr 1
        funext x
        exact G.apply_symm_apply (d x)
      _ = _ := by rw [← hd]; exact roundSphereDiscChart_image_closedBall _ _ _
  have hboundary : G '' (f '' sphere 0 1) =
      (stereographic' 2 (-v)).symm '' sphere 0 (4 / r) := by
    calc
      _ = d '' sphere 0 1 := by
        simp only [image_image]
        congr 1
        funext x
        exact G.apply_symm_apply (d x)
      _ = _ := by rw [← hd]; exact roundSphereDiscChart_image_sphere _ _ _
  have hvsource : closedBall (0 : E2) r ⊆ (stereographic' 2 v).symm.source := by
    rw [OpenPartialHomeomorph.symm_source, stereographic'_target]
    exact subset_univ _
  have heBoundary : G '' (e '' sphere 0 1) = (stereographic' 2 v).symm '' sphere 0 r := by
    rw [← compactChart_frontier_closedBall e 0 zero_lt_one he]
    change G.toHomeomorph '' frontier (e '' closedBall 0 1) = _
    rw [G.toHomeomorph.image_frontier]
    change frontier (G '' (e '' closedBall 0 1)) = _
    rw [hG, compactChart_frontier_closedBall _ 0 hr hvsource]
  obtain ⟨hunion, hinter, hbd⟩ := sphereStereo_complementary_discs v hr
  have hGi : Injective (G : UnitTwoSphere → UnitTwoSphere) := G.injective
  have hu : (e '' closedBall 0 1) ∪ (f '' closedBall 0 1) = univ := by
    apply hGi.image_injective
    rw [image_union, hG, hclosed]
    rw [show G '' (univ : Set UnitTwoSphere) = univ from
      image_univ_of_surjective G.surjective]
    exact hunion
  have hi : (e '' closedBall 0 1) ∩ (f '' closedBall 0 1) = e '' sphere 0 1 := by
    apply hGi.image_injective
    rw [image_inter hGi, hG, hclosed, heBoundary]
    exact hinter
  have hb : f '' sphere 0 1 = e '' sphere 0 1 := by
    apply hGi.image_injective
    rw [hboundary, heBoundary]
    exact hbd
  have hopen (k : OpenPartialHomeomorph E2 UnitTwoSphere)
      (hk : closedBall 0 1 ⊆ k.source) :
      k '' ball 0 1 = k '' closedBall 0 1 \ k '' sphere 0 1 := by
    rw [← (k.injOn.mono hk).image_sdiff_subset sphere_subset_closedBall,
      closedBall_sdiff_sphere]
  refine ⟨f, hfs, hfsm, hfsi, hu, hi, hb, ?_, ?_⟩
  · rw [hopen e he, hopen f hfc, hb]
    apply disjoint_left.mpr
    intro q hq hq'
    apply hq.2
    rw [← hi]
    exact ⟨hq.1, hq'.1⟩
  · rw [hopen e he, hopen f hfc, hb, ← union_sdiff_distrib, hu]
    ext p
    simp

end PoincareConjecture.M25.Topology3D
