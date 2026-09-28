import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.CirclePair.Ribbon.ExteriorEdge
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.BoundaryGerm.MarkingExtraction

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Nested

open CircleAttachmentGerm

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev S1 := sphere (0 : E2) 1

private theorem common_image_neighborhood
    (F G : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) {p : E2}
    (hFG : (F : E2 → E2) =ᶠ[𝓝 p] G) :
    ∃ U : Set E2, IsOpen U ∧ F p ∈ U ∧
      ∀ S : Set E2, U ∩ (F '' S) = U ∩ (G '' S) := by
  obtain ⟨V, hVeq, hV, hpV⟩ := _root_.mem_nhds_iff.mp hFG
  refine ⟨F '' V, F.toHomeomorph.isOpenMap _ hV, mem_image_of_mem _ hpV, ?_⟩
  intro S
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, z, hz, hzx⟩
    have heq : z = x := F.injective hzx
    subst z
    exact ⟨mem_image_of_mem _ hx, x, hz, (hVeq hx).symm⟩
  · rintro ⟨⟨x, hx, rfl⟩, z, hz, hzx⟩
    have heq : z = x := G.injective (hzx.trans (hVeq hx))
    subst z
    exact ⟨mem_image_of_mem _ hx, x, hz, rfl⟩

theorem exists_common_filled_side_of_inward_ribbon
    (A B R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {w : Real} (hw : 0 < w)
    (hAedge : ∀ s ∈ Ioo (-w) w,
      R (WithLp.toLp 2 ![s, 0]) ∈ A '' sphere (0 : E2) 1)
    (hBedge : ∀ s ∈ Ioo (-w) w,
      R (WithLp.toLp 2 ![s, 0]) ∈ B '' sphere (0 : E2) 1)
    (hAin : ∀ᶠ t in 𝓝[<] (0 : Real),
      R (WithLp.toLp 2 ![0, t]) ∈ A '' ball (0 : E2) 1)
    (hBin : ∀ᶠ t in 𝓝[<] (0 : Real),
      R (WithLp.toLp 2 ![0, t]) ∈ B '' ball (0 : E2) 1) :
    ∃ U : Set E2, IsOpen U ∧ R 0 ∈ U ∧
      U ∩ (A '' closedBall (0 : E2) 1) = U ∩ (B '' closedBall (0 : E2) 1) ∧
      U ∩ (A '' ball (0 : E2) 1) = U ∩ (B '' ball (0 : E2) 1) := by
  obtain ⟨F, hFc, hFo, _, hF⟩ :=
    exists_filling_adapted_to_ribbon_edge A R hw hAedge hAin
  obtain ⟨G, hGc, hGo, _, hG⟩ :=
    exists_filling_adapted_to_ribbon_edge B R hw hBedge hBin
  obtain ⟨U, hU, hpU, hUS⟩ := common_image_neighborhood F G (hF.trans hG.symm)
  have hp : F (upperPoint : E2) = R 0 := by
    have hzero : (WithLp.toLp 2 ![0, 0] : E2) = 0 := by ext i; fin_cases i <;> rfl
    have hflat : upperBoundaryFlattening (upperPoint : E2) = 0 := by
      simpa only [add_zero, one_smul, hzero] using upperBoundaryFlattening_radial 0
    simpa only [hflat] using hF.eq_of_nhds
  refine ⟨U, hU, hp ▸ hpU, ?_, ?_⟩
  · simpa only [hFc, hGc] using hUS (closedBall (0 : E2) 1)
  · simpa only [hFo, hGo] using hUS (ball (0 : E2) 1)

theorem exists_common_marks_of_inward_ribbon
    (A B R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {w : Real} (hw : 0 < w)
    (hAedge : ∀ s ∈ Ioo (-w) w,
      R (WithLp.toLp 2 ![s, 0]) ∈ A '' sphere (0 : E2) 1)
    (hBedge : ∀ s ∈ Ioo (-w) w,
      R (WithLp.toLp 2 ![s, 0]) ∈ B '' sphere (0 : E2) 1)
    (hAin : ∀ᶠ t in 𝓝[<] (0 : Real),
      R (WithLp.toLp 2 ![0, t]) ∈ A '' ball (0 : E2) 1)
    (hBin : ∀ᶠ t in 𝓝[<] (0 : Real),
      R (WithLp.toLp 2 ![0, t]) ∈ B '' ball (0 : E2) 1) :
    ∃ F G : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      F '' closedBall 0 1 = A '' closedBall 0 1 ∧
      G '' closedBall 0 1 = B '' closedBall 0 1 ∧
      (F : E2 → E2) =ᶠ[𝓝 (upperPoint : E2)] G ∧
      ∃ (f : E1 → S1) (V : Set E2),
        f 0 = upperPoint ∧ InjOn f (closedBall 0 2) ∧
        (∀ x ∈ closedBall (0 : E1) 2,
          IsLocalDiffeomorphAt (𝓡 1) (𝓡 1) ∞ f x) ∧
        (∀ x ∈ closedBall (0 : E1) 2, F (f x) = G (f x)) ∧
        IsOpen V ∧ (fun x => F (f x)) '' closedBall 0 2 ⊆ V ∧
        V ∩ (F '' closedBall 0 1) = V ∩ (G '' closedBall 0 1) ∧
        F (f 0) = R 0 := by
  obtain ⟨F, hFc, _, _, hF⟩ :=
    exists_filling_adapted_to_ribbon_edge A R hw hAedge hAin
  obtain ⟨G, hGc, _, _, hG⟩ :=
    exists_filling_adapted_to_ribbon_edge B R hw hBedge hBin
  have hFG := hF.trans hG.symm
  obtain ⟨W, hWeq, hW, hpW⟩ := _root_.mem_nhds_iff.mp hFG
  obtain ⟨V, hV, hpV, hVS⟩ := common_image_neighborhood F G hFG
  obtain ⟨f, hf0, hfi, hfl, hfg, hfV⟩ :=
    BoundaryGerm.exists_common_boundary_marking_of_eqOn F G upperPoint W hW hpW hWeq
      V hV hpV
  refine ⟨F, G, hFc, hGc, hFG, f, V, hf0, hfi, hfl, hfg, hV, hfV,
    hVS _, ?_⟩
  rw [hf0]
  have hzero : (WithLp.toLp 2 ![0, 0] : E2) = 0 := by ext i; fin_cases i <;> rfl
  have hflat : upperBoundaryFlattening (upperPoint : E2) = 0 := by
    simpa only [add_zero, one_smul, hzero] using upperBoundaryFlattening_radial 0
  simpa only [hflat] using hF.eq_of_nhds

theorem exists_common_filled_sides_of_annular_ribbon
    (A B R : Fin 2 → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {w : Real} (hw : 0 < w)
    (hAedge : ∀ i s, s ∈ Ioo (-w) w →
      R i (WithLp.toLp 2 ![s, 0]) ∈ A i '' sphere (0 : E2) 1)
    (hBedge : ∀ i s, s ∈ Ioo (-w) w →
      R i (WithLp.toLp 2 ![s, 0]) ∈ B i '' sphere (0 : E2) 1)
    (hannulus : ∀ i, ∀ᶠ t in 𝓝[>] (0 : Real),
      R i (WithLp.toLp 2 ![0, t]) ∈
        ((A 0 '' ball (0 : E2) 1) \ (A 1 '' closedBall (0 : E2) 1)) ∩
        ((B 0 '' ball (0 : E2) 1) \ (B 1 '' closedBall (0 : E2) 1))) :
    ∀ i, ∃ U : Set E2, IsOpen U ∧ R i 0 ∈ U ∧
      U ∩ (A i '' closedBall (0 : E2) 1) = U ∩ (B i '' closedBall (0 : E2) 1) ∧
      U ∩ (A i '' ball (0 : E2) 1) = U ∩ (B i '' ball (0 : E2) 1) := by
  intro i
  fin_cases i
  · have hneg : Tendsto (fun t : Real => -t) (𝓝[<] 0) (𝓝[>] 0) := by
      simpa using (tendsto_neg_nhdsLT_neg (a := (0 : Real)))
    have hin := hneg.eventually (hannulus 0)
    have hAin : ∀ᶠ t in 𝓝[<] (0 : Real),
        (ribbonTransverseReflection.trans (R 0)) (WithLp.toLp 2 ![0, t]) ∈
          A 0 '' ball (0 : E2) 1 := by
      filter_upwards [hin] with t ht
      exact ht.1.1
    have hBin : ∀ᶠ t in 𝓝[<] (0 : Real),
        (ribbonTransverseReflection.trans (R 0)) (WithLp.toLp 2 ![0, t]) ∈
          B 0 '' ball (0 : E2) 1 := by
      filter_upwards [hin] with t ht
      exact ht.2.1
    have hzero : ribbonTransverseReflection (0 : E2) = 0 := by
      change WithLp.toLp 2 ![(0 : E2) 0, -(0 : E2) 1] = 0
      ext i
      fin_cases i <;> simp
    obtain ⟨U, hU, hpU, hc, ho⟩ :=
      exists_common_filled_side_of_inward_ribbon (A 0) (B 0)
        (ribbonTransverseReflection.trans (R 0)) hw
        (by simpa using hAedge 0) (by simpa using hBedge 0) hAin hBin
    change (R 0) (ribbonTransverseReflection 0) ∈ U at hpU
    exact ⟨U, hU, hzero ▸ hpU, hc, ho⟩
  · exact exists_common_filled_side_of_inward_ribbon (A 1) (B 1) (R 1) hw
      (hAedge 1) (hBedge 1)
      (ribbon_inward_germ_of_exterior_edge (A 1) (R 1) hw (hAedge 1)
        ((hannulus 1).mono (fun _ ht => ht.1.2)))
      (ribbon_inward_germ_of_exterior_edge (B 1) (R 1) hw (hBedge 1)
        ((hannulus 1).mono (fun _ ht => ht.2.2)))

end Poincare.Manifold.Schoenflies.PlaneArcs.Nested
