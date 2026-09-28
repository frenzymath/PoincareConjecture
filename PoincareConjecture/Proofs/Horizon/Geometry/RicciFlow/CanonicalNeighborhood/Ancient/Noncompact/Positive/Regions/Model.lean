import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Regions.Ball
import Mathlib.Analysis.InnerProductSpace.Calculus









set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.NoncompactKappa.Positive.SoulNeckRegion

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}
  {S : RiemannianMetric.PointSoulData (K.flow.metric 0)} {epsilon D R : ℝ}
  (G : SoulNeckRegion K S epsilon D R)


theorem exists_inside_euclidean_coordinates :
    ∃ e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) M,
      e.source = univ ∧ e.target = G.inside ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target := by
  obtain ⟨b, hbs, _, hb, hbi, _, hbball, _⟩ := G.exists_closed_side_ball_neighborhood
  let a : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3))
      (EuclideanSpace ℝ (Fin 3)) := OpenPartialHomeomorph.univUnitBall
  have haball (x : EuclideanSpace ℝ (Fin 3)) : a x ∈ Metric.ball 0 1 :=
    a.map_source (mem_univ x)
  have has (x : EuclideanSpace ℝ (Fin 3)) : a x ∈ b.source :=
    hbs (Metric.ball_subset_closedBall (haball x))
  have hes : (a.trans b).source = univ := by
    ext x
    exact iff_of_true ⟨mem_univ _, has x⟩ (mem_univ _)
  have het : (a.trans b).target = G.inside := by
    ext x
    constructor
    · rintro ⟨hxb, hxball⟩
      rw [← hbball]
      exact ⟨b.symm x, hxball, b.right_inv hxb⟩
    · intro hx
      obtain ⟨y, hy, rfl⟩ := hbball.symm ▸ hx
      have hyb := hbs (Metric.ball_subset_closedBall hy)
      refine ⟨b.map_source hyb, ?_⟩
      change b.symm (b y) ∈ Metric.ball 0 1
      rwa [b.left_inv hyb]
  refine ⟨a.trans b, hes, het, ?_, ?_⟩
  · exact hb.comp OpenPartialHomeomorph.contDiff_univUnitBall.contMDiff.contMDiffOn
      (fun x _ => has x)
  · exact OpenPartialHomeomorph.contDiffOn_univUnitBall_symm.contMDiffOn.comp
      (hbi.mono (fun x hx => hx.1)) (fun x hx => hx.2)


theorem nonempty_capModel_image_inside (F : Diffeomorph (𝓡 3) (𝓡 3) M M ∞)
    (p : RealProjectiveThree) :
    Nonempty (CapModelEquivalence .euclidean p (F '' G.inside)) := by
  obtain ⟨e, hes, het, he, hei⟩ := G.exists_inside_euclidean_coordinates
  refine ⟨{
    model := M
    model_topology := inferInstance
    model_charted := inferInstance
    model_manifold := inferInstance
    standard_model := S.euclidean.symm.toHomeomorph.trans Homeomorph.ulift.symm
    standard_smooth := ⟨S.euclidean.symm⟩
    forward := fun x => S.euclidean (e.symm (F.symm x))
    inverse := fun y => F (e (S.euclidean.symm y))
    inverse_mem := ?_
    left_inverse := ?_
    right_inverse := ?_
    forward_smooth := ?_
    inverse_smooth := ?_ }⟩
  · intro y
    exact mem_image_of_mem F (het ▸ e.map_source (hes ▸ mem_univ _))
  · rintro _ ⟨x, hx, rfl⟩
    rw [F.symm_apply_apply, S.euclidean.symm_apply_apply,
      e.right_inv (het.symm ▸ hx)]
  · intro y
    rw [F.symm_apply_apply, e.left_inv (hes ▸ mem_univ _),
      S.euclidean.apply_symm_apply]
  · apply S.euclidean.contMDiff.comp_contMDiffOn
    apply hei.comp F.symm.contMDiff.contMDiffOn
    rintro _ ⟨x, hx, rfl⟩
    change F.symm (F x) ∈ e.target
    rw [F.symm_apply_apply, het]
    exact hx
  · apply F.contMDiff.comp_contMDiffOn
    exact he.comp S.euclidean.symm.contMDiff.contMDiffOn (fun _ _ => hes ▸ mem_univ _)

end PoincareConjecture.NoncompactKappa.Positive.SoulNeckRegion
