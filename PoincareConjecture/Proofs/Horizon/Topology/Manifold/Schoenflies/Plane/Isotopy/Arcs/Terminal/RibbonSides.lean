import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.BoundaryGerm.Gap
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.CirclePair.Ribbon.ExteriorEdge

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

open CircleAttachmentGerm

private abbrev E2 := EuclideanSpace Real (Fin 2)

private def shiftRibbonParameter (s : Real) : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ where
  toFun x := WithLp.toLp 2 ![s + x 0, x 1]
  invFun x := WithLp.toLp 2 ![x 0 - s, x 1]
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv x := by ext i; fin_cases i <;> simp
  contMDiff_toFun := by
    apply ContDiff.contMDiff
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact contDiff_const.add (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff
    · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff
  contMDiff_invFun := by
    apply ContDiff.contMDiff
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff.sub contDiff_const
    · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff

private theorem exists_filled_coincidence_of_exterior_edge
    (A B R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {w : Real} (hw : 0 < w)
    (hAedge : ∀ s ∈ Ioo (-w) w,
      R (WithLp.toLp 2 ![s, 0]) ∈ A '' sphere (0 : E2) 1)
    (hBedge : ∀ s ∈ Ioo (-w) w,
      R (WithLp.toLp 2 ![s, 0]) ∈ B '' sphere (0 : E2) 1)
    (hAout : ∀ᶠ t in 𝓝[>] (0 : Real),
      R (WithLp.toLp 2 ![0, t]) ∉ A '' closedBall (0 : E2) 1)
    (hBout : ∀ᶠ t in 𝓝[>] (0 : Real),
      R (WithLp.toLp 2 ![0, t]) ∉ B '' closedBall (0 : E2) 1) :
    ∃ W : Set E2, IsOpen W ∧ R 0 ∈ W ∧
      W ∩ (A '' closedBall 0 1) = W ∩ (B '' closedBall 0 1) := by
  obtain ⟨F, hFc, _, _, hF⟩ :=
    exists_filling_adapted_to_exterior_ribbon_edge A R hw hAedge hAout
  obtain ⟨G, hGc, _, _, hG⟩ :=
    exists_filling_adapted_to_exterior_ribbon_edge B R hw hBedge hBout
  obtain ⟨U, hUeq, hU, hpU⟩ := _root_.mem_nhds_iff.mp (hF.trans hG.symm)
  have hpF : F upperPoint = R 0 := by
    have h := hF.self_of_nhds
    have hz : (WithLp.toLp 2 ![0, 0] : E2) = 0 := by ext i; fin_cases i <;> rfl
    simpa [upperBoundaryFlattening, upperPoint, hz] using h
  refine ⟨F '' U, F.toHomeomorph.isOpenMap _ hU,
    hpF ▸ mem_image_of_mem F hpU, ?_⟩
  apply Subset.antisymm
  · rintro y ⟨⟨x, hx, rfl⟩, hy⟩
    rw [← hFc] at hy
    obtain ⟨z, hz, heq⟩ := hy
    have hzx : z = x := F.injective heq
    subst z
    refine ⟨mem_image_of_mem F hx, ?_⟩
    rw [← hGc]
    exact ⟨x, hz, (hUeq hx).symm⟩
  · rintro y ⟨⟨x, hx, rfl⟩, hy⟩
    rw [← hGc] at hy
    obtain ⟨z, hz, heq⟩ := hy
    have hzx : z = x := G.injective (heq.trans (hUeq hx))
    subst z
    refine ⟨mem_image_of_mem F hx, ?_⟩
    rw [← hFc]
    exact mem_image_of_mem F hz

theorem exists_filled_coincidence_of_shared_unnested_ribbon
    (A B : Fin 2 → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hA : Disjoint (A 0 '' closedBall 0 1) (A 1 '' closedBall 0 1))
    (hB : Disjoint (B 0 '' closedBall 0 1) (B 1 '' closedBall 0 1))
    (R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {w : Real} (_hw : 0 < w)
    (hedge : ∀ s ∈ Ioo (-w) w, R (WithLp.toLp 2 ![s, 0]) ∈
      (A 0 '' sphere (0 : E2) 1) ∩ (B 0 '' sphere (0 : E2) 1))
    (hfinish : ∀ s ∈ Ioo (-w) w, R (WithLp.toLp 2 ![s, 1]) ∈
      (A 1 '' closedBall (0 : E2) 1) ∩ (B 1 '' closedBall (0 : E2) 1))
    (havoid : ∀ s ∈ Ioo (-w) w,
      Disjoint ((fun t : Real => R (WithLp.toLp 2 ![s, t])) '' Ioo 0 1)
        ((frontier (A 0 '' closedBall 0 1) ∪ frontier (A 1 '' closedBall 0 1)) ∪
          (frontier (B 0 '' closedBall 0 1) ∪ frontier (B 1 '' closedBall 0 1)))) :
    ∃ V : Set E2, IsOpen V ∧
      (fun s : Real => R (WithLp.toLp 2 ![s, 0])) '' Ioo (-w) w ⊆ V ∧
      V ∩ (A 0 '' closedBall 0 1) = V ∩ (B 0 '' closedBall 0 1) := by
  classical
  have hlocal (s : Ioo (-w) w) : ∃ W : Set E2, IsOpen W ∧
      R (WithLp.toLp 2 ![(s : Real), 0]) ∈ W ∧
      W ∩ (A 0 '' closedBall 0 1) = W ∩ (B 0 '' closedBall 0 1) := by
    let β : Real → E2 := fun t => R (WithLp.toLp 2 ![(s : Real), t])
    have hβ : Continuous β := R.continuous.comp (by fun_prop)
    have hAout := BoundaryGerm.connector_image_subset_compl_of_disjoint_closed
      ((isCompact_closedBall _ _).image (A 0).continuous).isClosed
      ((isCompact_closedBall _ _).image (A 1).continuous).isClosed hA hβ.continuousOn
      (image_mono sphere_subset_closedBall (hedge s s.property).1)
      (hfinish s s.property).1 ((havoid s s.property).mono_right subset_union_left)
    have hBout := BoundaryGerm.connector_image_subset_compl_of_disjoint_closed
      ((isCompact_closedBall _ _).image (B 0).continuous).isClosed
      ((isCompact_closedBall _ _).image (B 1).continuous).isClosed hB hβ.continuousOn
      (image_mono sphere_subset_closedBall (hedge s s.property).2)
      (hfinish s s.property).2 ((havoid s s.property).mono_right subset_union_right)
    let ε := min ((s : Real) + w) (w - s)
    have hε : 0 < ε := lt_min (by linarith [s.property.1]) (by linarith [s.property.2])
    have hshift {u : Real} (hu : u ∈ Ioo (-ε) ε) :
        (s : Real) + u ∈ Ioo (-w) w := by
      have hl := min_le_left ((s : Real) + w) (w - s)
      have hr := min_le_right ((s : Real) + w) (w - s)
      change -ε < u ∧ u < ε at hu
      constructor <;> dsimp [ε] at hu <;> linarith
    have hedgeA : ∀ u ∈ Ioo (-ε) ε,
        ((shiftRibbonParameter s).trans R) (WithLp.toLp 2 ![u, 0]) ∈
          A 0 '' sphere (0 : E2) 1 := by
      intro u hu
      exact (hedge _ (hshift hu)).1
    have hedgeB : ∀ u ∈ Ioo (-ε) ε,
        ((shiftRibbonParameter s).trans R) (WithLp.toLp 2 ![u, 0]) ∈
          B 0 '' sphere (0 : E2) 1 := by
      intro u hu
      exact (hedge _ (hshift hu)).2
    obtain ⟨W, hW, hpW, hside⟩ := exists_filled_coincidence_of_exterior_edge
      (A 0) (B 0) ((shiftRibbonParameter s).trans R) hε hedgeA hedgeB
      (by
        filter_upwards [Ioo_mem_nhdsGT (show (0 : Real) < 1 by norm_num)] with t ht
        intro hm
        apply hAout (mem_image_of_mem β ht)
        apply Or.inl
        change R (WithLp.toLp 2 ![(s : Real) + 0, t]) ∈ _ at hm
        simpa only [add_zero] using hm)
      (by
        filter_upwards [Ioo_mem_nhdsGT (show (0 : Real) < 1 by norm_num)] with t ht
        intro hm
        apply hBout (mem_image_of_mem β ht)
        apply Or.inl
        change R (WithLp.toLp 2 ![(s : Real) + 0, t]) ∈ _ at hm
        simpa only [add_zero] using hm)
    change R (WithLp.toLp 2 ![(s : Real) + 0, 0]) ∈ W at hpW
    exact ⟨W, hW, by simpa only [add_zero] using hpW, hside⟩
  choose W hW hpW hside using hlocal
  refine ⟨⋃ s, W s, isOpen_iUnion hW, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact mem_iUnion.mpr ⟨⟨s, hs⟩, hpW ⟨s, hs⟩⟩
  · ext x
    constructor
    · rintro ⟨hx, hxa⟩
      obtain ⟨s, hs⟩ := mem_iUnion.mp hx
      exact ⟨mem_iUnion.mpr ⟨s, hs⟩, ((hside s) ▸ (show x ∈ W s ∩ _ from ⟨hs, hxa⟩)).2⟩
    · rintro ⟨hx, hxb⟩
      obtain ⟨s, hs⟩ := mem_iUnion.mp hx
      exact ⟨mem_iUnion.mpr ⟨s, hs⟩, ((hside s).symm ▸ (show x ∈ W s ∩ _ from ⟨hs, hxb⟩)).2⟩

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
