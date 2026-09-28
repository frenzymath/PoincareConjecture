import PoincareConjecture.Proofs.M11.OrdinaryAtlas
import PoincareConjecture.Proofs.M11.OrdinaryChartHomeomorph
import PoincareConjecture.Proofs.M11.SpacetimeGeometry





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T2Space M] [SecondCountableTopology M] [Nonempty M]

theorem ordinaryProduct_forward_smooth (g : ℝ → RiemannianMetric n M)
    (I : SpacetimeInterval) (hg : RiemannianMetric.IsSmoothFamilyOn g I.domain) :
    ContMDiff (M := (smoothInterval I).Point × M)
      (M' := (adaptedSpacetime (ordinaryAtlas g I hg)).Point)
      (spacetimeModel n) (spacetimeModel n) ∞
      (fun p : (smoothInterval I).Point × M ↦
        (p : (adaptedSpacetime (ordinaryAtlas g I hg)).Point)) := by
  intro p
  let A := ordinaryAtlas g I hg
  let := intervalChartedSpace I
  let e := spatialChartHomeomorph (n := n) p.2
  have hp : p.2 ∈ e.target := by
    rw [spatialChartHomeomorph_target]
    exact mem_chart_source _ p.2
  have hi := (spatialChartHomeomorph_inverse_smooth p.2).contMDiffAt
    (e.open_target.mem_nhds hp)
  have hbox : ContMDiff (M := (smoothInterval I).Point × spatialChartDomain (n := n) p.2)
      (M' := (adaptedSpacetime A).Point) (spacetimeModel n) (spacetimeModel n) ∞
      (fun q ↦ (ordinaryBox g I hg p.2).toSpacetime q) := by
    let := intervalChartedSpace (A.box p.2).interval
    let := adaptedChartedSpace A
    exact (adapted_box_localDiffeomorph A p.2).contMDiff
  have hlocal := hbox.contMDiffAt.comp p
    (contMDiffAt_fst.prodMk (hi.comp p contMDiffAt_snd))
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [(e.open_target.preimage continuous_snd).mem_nhds hp] with q hq
  apply Prod.ext
  · rfl
  · exact (e.right_inv hq).symm

theorem ordinaryProduct_inverse_smooth (g : ℝ → RiemannianMetric n M)
    (I : SpacetimeInterval) (hg : RiemannianMetric.IsSmoothFamilyOn g I.domain) :
    ContMDiff (M := (adaptedSpacetime (ordinaryAtlas g I hg)).Point)
      (M' := (smoothInterval I).Point × M)
      (spacetimeModel n) (spacetimeModel n) ∞
      (fun p : (adaptedSpacetime (ordinaryAtlas g I hg)).Point ↦
        (p : (smoothInterval I).Point × M)) := by
  let A := ordinaryAtlas g I hg
  let := intervalChartedSpace I
  apply (cover_smooth_iff (J := spacetimeModel n) (L := spacetimeModel n)
    (N := (smoothInterval I).Point × M) (fun b ↦ boxHomeomorph (A.box b))
    (box_targets_cover A) (box_transition_smooth A) _).mpr
  intro b
  change M at b
  change ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞
    (fun q : (smoothInterval I).Point × spatialChartDomain (n := n) b ↦
      (q.1, spatialChartInverse b q.2)) univ
  exact (contMDiff_fst.prodMk ((spatialChartInverse_smooth b).comp contMDiff_snd)).contMDiffOn

noncomputable def ordinaryProductIdentification (g : ℝ → RiemannianMetric n M)
    (I : SpacetimeInterval) (hg : RiemannianMetric.IsSmoothFamilyOn g I.domain) :
    Diffeomorph (spacetimeModel n) (spacetimeModel n) ((smoothInterval I).Point × M)
      (adaptedSpacetime (ordinaryAtlas g I hg)).Point ∞ where
  toEquiv := Equiv.refl _
  contMDiff_toFun := ordinaryProduct_forward_smooth g I hg
  contMDiff_invFun := ordinaryProduct_inverse_smooth g I hg

end PoincareConjecture.Proofs.M11
