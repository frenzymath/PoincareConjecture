import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Topology



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1



structure SphereSurgeryCoreCap (v : E3) (g : S2 → E3) (B : Set Real) where
  chart : OpenPartialHomeomorph E2 S2
  source : closedBall 0 1 ⊆ chart.source
  smooth : ContMDiffOn (𝓡 2) (𝓡 2) ∞ chart chart.source
  symm_smooth : ContMDiffOn (𝓡 2) (𝓡 2) ∞ chart.symm chart.target
  unit_v : ‖v‖ = 1
  center : Real
  scale : Real
  scale_ne_zero : scale ≠ 0
  planeMap : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
    (Hemisphere.Plane v) (Hemisphere.Plane v) ∞
  parametrization : E2 → E3
  parametrization_smooth : ContDiff Real ∞ parametrization
  parametrization_injective : Injective parametrization
  parametrization_deriv_injective : ∀ x, Injective (fderiv Real parametrization x)
  parametrization_eq : ∀ x ∈ closedBall 0 1, g (chart x) = parametrization x
  boundary_height : ∀ x ∈ sphere (0 : E2) 1, inner Real v (parametrization x) = center
  range_eq : parametrization '' closedBall (0 : E2) 1 =
    Poincare.Geometry.Euclidean.liftPlaneDiffeomorph unit_v center scale scale_ne_zero planeMap ''
      ((fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
        {p : S2 | 0 ≤ inner Real v (p : E3)})
  avoids_protected : ∀ x ∈ closedBall 0 1, inner Real v (parametrization x) ∉ B

namespace SphereSurgeryStep

variable {f : S2 → E3} {v : E3} {c R : Real} (S : SphereSurgeryStep f v c R)

theorem capMinus_boundary_height {x : E2} (hx : x ∈ sphere (0 : E2) 1) :
    inner Real v (S.gMinus x) = c - S.a := by
  have hb : S.dMinus '' sphere (0 : E2) 1 = S.eMinus '' sphere (0 : E2) 1 := by
    rw [S.dMinus.image_sphere_eq_frontier S.dMinus_source rfl, S.dMinus_closed,
      frontier_compl, ParallelDisks.frontier_image_ball zero_lt_one S.eMinus
        S.eMinus_source S.eMinus_smooth S.eMinus_symm_smooth]
  have hxret : S.dMinus x ∈ S.eMinus '' sphere (0 : E2) 1 :=
    hb ▸ mem_image_of_mem _ hx
  have hxtube := hxret
  rw [S.eMinus_boundary] at hxtube
  obtain ⟨q, hq⟩ := hxtube
  have ht : -S.a ∈ Ioo (-S.ε) S.ε := by
    constructor <;> linarith [S.a_pos, S.ε_pos, S.a_lt_quarter_ε]
  rw [← S.capMinus_eq x (sphere_subset_closedBall hx),
    S.retainedMinus_eq _ (image_mono sphere_subset_closedBall hxret),
    S.height_preserving, ← hq, S.tube_height q (-S.a) ht]
  rfl

theorem capPlus_boundary_height {x : E2} (hx : x ∈ sphere (0 : E2) 1) :
    inner Real v (S.gPlus x) = c + S.a := by
  have hb : S.dPlus '' sphere (0 : E2) 1 = S.ePlus '' sphere (0 : E2) 1 := by
    rw [S.dPlus.image_sphere_eq_frontier S.dPlus_source rfl, S.dPlus_closed,
      frontier_compl, ParallelDisks.frontier_image_ball zero_lt_one S.ePlus
        S.ePlus_source S.ePlus_smooth S.ePlus_symm_smooth]
  have hxret : S.dPlus x ∈ S.ePlus '' sphere (0 : E2) 1 :=
    hb ▸ mem_image_of_mem _ hx
  have hxtube := hxret
  rw [S.ePlus_boundary] at hxtube
  obtain ⟨q, hq⟩ := hxtube
  have ht : S.a ∈ Ioo (-S.ε) S.ε := by
    constructor <;> linarith [S.a_pos, S.ε_pos, S.a_lt_quarter_ε]
  rw [← S.capPlus_eq x (sphere_subset_closedBall hx),
    S.retainedPlus_eq _ (image_mono sphere_subset_closedBall hxret),
    S.height_preserving, ← hq, S.tube_height q S.a ht]

end SphereSurgeryStep

namespace SphereSurgeryCoreCap

variable {v : E3} {g : S2 → E3} {B : Set Real}

theorem image_closedBall (D : SphereSurgeryCoreCap v g B) :
    g '' (D.chart '' closedBall 0 1) = D.parametrization '' closedBall 0 1 := by
  rw [← image_comp]
  exact image_congr D.parametrization_eq

theorem disjoint_protected_heights (D : SphereSurgeryCoreCap v g B) :
    Disjoint ((fun p => inner Real v (g p)) '' (D.chart '' closedBall 0 1)) B := by
  apply Set.disjoint_left.mpr
  rintro k ⟨p, ⟨x, hx, rfl⟩, rfl⟩ hk
  dsimp only at hk
  rw [D.parametrization_eq x hx] at hk
  exact D.avoids_protected x hx hk

private theorem adjoin_to_complement {C : Set S2}
    (D : SphereSurgeryCoreCap v g B) (L : List (SphereSurgeryCoreCap v g B))
    (hpair : L.Pairwise (fun D E => Disjoint
      (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)))
    (hC : C = (⋃ E ∈ L, E.chart '' ball 0 1)ᶜ)
    (hin : D.chart '' closedBall 0 1 ⊆ interior C) :
    (D :: L).Pairwise (fun D E => Disjoint
      (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)) ∧
    C ∩ (D.chart '' ball 0 1)ᶜ = (⋃ E ∈ D :: L, E.chart '' ball 0 1)ᶜ := by
  refine ⟨List.pairwise_cons.mpr ⟨?_, hpair⟩, ?_⟩
  · intro E hE
    have hdis : Disjoint (E.chart '' ball 0 1) (interior C) := by
      apply Set.disjoint_left.mpr
      intro p hp hpi
      have hpC := interior_subset hpi
      rw [hC] at hpC
      exact hpC (mem_iUnion_of_mem E (mem_iUnion_of_mem hE hp))
    have hclosed := hdis.closure_left isOpen_interior
    rw [ParallelDisks.closure_image_ball zero_lt_one E.chart E.source] at hclosed
    exact (hclosed.mono_right hin).symm
  · rw [hC]
    ext p
    simp only [mem_inter_iff, mem_compl_iff, mem_iUnion, List.mem_cons]
    constructor
    · rintro ⟨hL, hD⟩ ⟨E, hE, hp⟩
      rcases hE with rfl | hE
      · exact hD hp
      · exact hL ⟨E, hE, hp⟩
    · intro h
      exact ⟨fun ⟨E, hE, hp⟩ => h ⟨E, Or.inr hE, hp⟩,
        fun hp => h ⟨D, Or.inl rfl, hp⟩⟩

end SphereSurgeryCoreCap

namespace SphereSurgeryPath

variable {v : E3} {f g : S2 → E3} {B : Set Real}



theorem exists_model_cap_complement (P : SphereSurgeryPath v f g)
    (hcaps : P.PreservesCaps) (hprotects : P.Protects B) :
    ∃ L : List (SphereSurgeryCoreCap v g B),
      L.Pairwise (fun D E => Disjoint
        (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)) ∧
      P.core = (⋃ D ∈ L, D.chart '' ball 0 1)ᶜ := by
  induction P with
  | refl => exact ⟨[], by simp, by simp [core]⟩
  | minus S next ih =>
    obtain ⟨L, hpair, hcore⟩ := ih hcaps.2 hprotects.2
    have hconn : IsPreconnected (S.dMinus '' closedBall 0 1) :=
      ((isConnected_closedBall (by norm_num : (0 : Real) ≤ 1)).image S.dMinus
        (S.dMinus.continuousOn.mono S.dMinus_source)).isPreconnected
    have hheight : ∀ p ∈ S.dMinus '' closedBall 0 1,
        inner Real v (S.fMinus p) ∈ S.capMinusHeights := by
      rintro p ⟨x, hx, rfl⟩
      rw [S.capMinus_eq x hx]
      exact ⟨x, hx, rfl⟩
    rcases next.protected_preconnected_core_dichotomy hcaps.1 hconn hheight with
      ⟨hin, heq⟩ | hout
    · let D : SphereSurgeryCoreCap v _ B := {
        chart := S.dMinus
        source := S.dMinus_source
        smooth := S.dMinus_smooth
        symm_smooth := S.dMinus_symm_smooth
        unit_v := S.unit_v
        center := _
        scale := S.s
        scale_ne_zero := S.s_pos.ne'
        planeMap := S.A
        parametrization := S.gMinus
        parametrization_smooth := S.gMinus_smooth
        parametrization_injective := S.gMinus_injective
        parametrization_deriv_injective := S.gMinus_deriv_injective
        parametrization_eq := fun x hx =>
          (heq _ (mem_image_of_mem _ hx)).self_of_nhds.trans (S.capMinus_eq x hx)
        boundary_height := fun _ hx => S.capMinus_boundary_height hx
        range_eq := S.gMinus_range
        avoids_protected := fun x _ hx => S.capMinus_avoids_of_far (hprotects.1 _ hx) x rfl }
      obtain ⟨hpair', hcore'⟩ := D.adjoin_to_complement L hpair hcore hin
      refine ⟨D :: L, hpair', ?_⟩
      simpa only [D, core, S.dMinus_open, compl_compl] using hcore'
    · refine ⟨L, hpair, ?_⟩
      rw [core, ← hcore]
      apply inter_eq_left.mpr
      intro p hp
      have hn : p ∉ S.dMinus '' ball 0 1 := fun hd =>
        Set.disjoint_left.mp hout (image_mono ball_subset_closedBall hd) hp
      simpa only [S.dMinus_open, mem_compl_iff, not_not] using hn
  | plus S next ih =>
    obtain ⟨L, hpair, hcore⟩ := ih hcaps.2 hprotects.2
    have hconn : IsPreconnected (S.dPlus '' closedBall 0 1) :=
      ((isConnected_closedBall (by norm_num : (0 : Real) ≤ 1)).image S.dPlus
        (S.dPlus.continuousOn.mono S.dPlus_source)).isPreconnected
    have hheight : ∀ p ∈ S.dPlus '' closedBall 0 1,
        inner Real v (S.fPlus p) ∈ S.capPlusHeights := by
      rintro p ⟨x, hx, rfl⟩
      rw [S.capPlus_eq x hx]
      exact ⟨x, hx, rfl⟩
    rcases next.protected_preconnected_core_dichotomy hcaps.1 hconn hheight with
      ⟨hin, heq⟩ | hout
    · let D : SphereSurgeryCoreCap v _ B := {
        chart := S.dPlus
        source := S.dPlus_source
        smooth := S.dPlus_smooth
        symm_smooth := S.dPlus_symm_smooth
        unit_v := S.unit_v
        center := _
        scale := -S.s
        scale_ne_zero := neg_ne_zero.mpr S.s_pos.ne'
        planeMap := S.A
        parametrization := S.gPlus
        parametrization_smooth := S.gPlus_smooth
        parametrization_injective := S.gPlus_injective
        parametrization_deriv_injective := S.gPlus_deriv_injective
        parametrization_eq := fun x hx =>
          (heq _ (mem_image_of_mem _ hx)).self_of_nhds.trans (S.capPlus_eq x hx)
        boundary_height := fun _ hx => S.capPlus_boundary_height hx
        range_eq := S.gPlus_range
        avoids_protected := fun x _ hx => S.capPlus_avoids_of_far (hprotects.1 _ hx) x rfl }
      obtain ⟨hpair', hcore'⟩ := D.adjoin_to_complement L hpair hcore hin
      refine ⟨D :: L, hpair', ?_⟩
      simpa only [D, core, S.dPlus_open, compl_compl] using hcore'
    · refine ⟨L, hpair, ?_⟩
      rw [core, ← hcore]
      apply inter_eq_left.mpr
      intro p hp
      have hn : p ∉ S.dPlus '' ball 0 1 := fun hd =>
        Set.disjoint_left.mp hout (image_mono ball_subset_closedBall hd) hp
      simpa only [S.dPlus_open, mem_compl_iff, not_not] using hn

end SphereSurgeryPath

namespace SphereSurgeryTree

variable {v : E3} {A : Finset Real} {f g : S2 → E3} {B : Set Real}



theorem exists_model_cap_core_to_leaf
    (tree : SphereSurgeryTree v A f) (hg : g ∈ tree.leaves)
    (hprotects : tree.Protects B) (hcaps : tree.PreservesCaps) :
    ∃ (P : SphereSurgeryPath v f g) (L : List (SphereSurgeryCoreCap v g B)),
      P.Protects B ∧ P.PreservesCaps ∧ IsConnected P.core ∧
      L.Pairwise (fun D E => Disjoint
        (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)) ∧
      P.core = (⋃ D ∈ L, D.chart '' ball 0 1)ᶜ := by
  obtain ⟨P, hP, hPC⟩ := tree.exists_cap_preserving_path_to_leaf hg hprotects hcaps
  obtain ⟨L, hpair, hcore⟩ := P.exists_model_cap_complement hPC hP
  exact ⟨P, L, hP, hPC, P.isConnected_core hPC, hpair, hcore⟩

end SphereSurgeryTree

end Poincare.Manifold.Schoenflies
