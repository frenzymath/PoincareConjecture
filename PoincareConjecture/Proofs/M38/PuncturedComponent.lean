import PoincareConjecture.Proofs.M38.ChartBall
import PoincareConjecture.Proofs.M38.ComponentBalls
import PoincareConjecture.Proofs.M38.BallPuncture
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.Connected










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38



theorem punctured_standard_ball_connected (r : ℝ) (hr : 0 < r) :
    IsConnected (Metric.ball (0 : StandardCapSpace) r \ {0}) := by
  let e := OpenPartialHomeomorph.univBall (0 : StandardCapSpace) r
  have hsource : e.source = Set.univ := OpenPartialHomeomorph.univBall_source _ _
  have htarget : e.target = Metric.ball (0 : StandardCapSpace) r :=
    OpenPartialHomeomorph.univBall_target _ hr
  have hzero : e 0 = 0 := OpenPartialHomeomorph.univBall_apply_zero _ _
  have himage : e '' ({0} : Set StandardCapSpace)ᶜ = Metric.ball 0 r \ {0} := by
    apply Set.Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      have hxs : x ∈ e.source := hsource.symm ▸ Set.mem_univ x
      have hzs : (0 : StandardCapSpace) ∈ e.source := hsource.symm ▸ Set.mem_univ 0
      refine ⟨htarget ▸ e.map_source hxs, ?_⟩
      intro hy
      have heq : e x = e 0 := (show e x = 0 from hy).trans hzero.symm
      exact hx (e.injOn hxs hzs heq)
    · intro y hy
      have hyt : y ∈ e.target := htarget.symm ▸ hy.1
      refine ⟨e.symm y, ?_, e.right_inv hyt⟩
      intro hz
      have hz0 : e.symm y = 0 := hz
      apply hy.2
      calc
        y = e (e.symm y) := (e.right_inv hyt).symm
        _ = e 0 := congrArg e hz0
        _ = 0 := hzero
  rw [← himage]
  exact (isConnected_compl_singleton_of_one_lt_rank (E := StandardCapSpace)
    (Module.one_lt_rank_of_one_lt_finrank (by simp [StandardCapSpace])) (0 : StandardCapSpace)).image e
      (OpenPartialHomeomorph.continuous_univBall _ _).continuousOn

variable {A : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A)



theorem surgeryBall_punctured_image :
    B.map '' (Metric.ball (0 : StandardCapSpace) 2 \ {0}) =
      (B.map '' Metric.ball (0 : StandardCapSpace) 2) \ {B.map 0} := by
  apply Set.Subset.antisymm
  · rintro y ⟨z, hz, rfl⟩
    refine ⟨⟨z, hz.1, rfl⟩, ?_⟩
    intro heq
    have hz0 : z = 0 := by
      calc
        z = B.inverse (B.map z) := (B.left_inverse hz.1).symm
        _ = B.inverse (B.map 0) := congrArg B.inverse (show B.map z = B.map 0 from heq)
        _ = 0 := B.left_inverse (by simp)
    exact hz.2 hz0
  · rintro y ⟨⟨z, hz, hzy⟩, hy⟩
    refine ⟨z, ⟨hz, ?_⟩, hzy⟩
    intro hz0
    exact hy (hzy.symm.trans (congrArg B.map (show z = 0 from hz0)))


theorem surgeryBall_punctured_image_connected :
    IsConnected ((B.map '' Metric.ball (0 : StandardCapSpace) 2) \ {B.map 0}) := by
  rw [← surgeryBall_punctured_image B]
  exact (punctured_standard_ball_connected 2 (by norm_num)).image B.map
    (B.map_smooth.continuousOn.mono Set.diff_subset)




theorem preconnected_diff_singleton_of_local
    {X : Type*} [TopologicalSpace X] [T1Space X]
    {C W : Set X} {p : X} (hC : IsPreconnected C) (hpC : p ∈ C)
    (hW : IsOpen W) (hpW : p ∈ W) (hWC : W ⊆ C)
    (hpunct : IsPreconnected (W \ {p})) : IsPreconnected (C \ {p}) := by
  apply isPreconnected_iff_subset_of_disjoint.mpr
  intro u v hu hv hcover hdisjoint
  have hlocalcover : W \ {p} ⊆ u ∪ v :=
    fun x hx => hcover ⟨hWC hx.1, hx.2⟩
  have hlocaldisjoint : (W \ {p}) ∩ (u ∩ v) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hbad : x ∈ (C \ {p}) ∩ (u ∩ v) := ⟨⟨hWC hx.1.1, hx.1.2⟩, hx.2⟩
    simpa only [hdisjoint, Set.mem_empty_iff_false] using hbad
  have hside (a b : Set X) (ha : IsOpen a) (hb : IsOpen b)
      (hcover' : C \ {p} ⊆ a ∪ b) (hdisjoint' : (C \ {p}) ∩ (a ∩ b) = ∅)
      (hWa : W \ {p} ⊆ a) : C \ {p} ⊆ a := by
    have hfullcover : C ⊆ (a ∪ W) ∪ (b \ {p}) := by
      intro x hx
      by_cases hxp : x = p
      · exact Or.inl (Or.inr (hxp.symm ▸ hpW))
      · rcases hcover' ⟨hx, hxp⟩ with hxa | hxb
        · exact Or.inl (Or.inl hxa)
        · exact Or.inr ⟨hxb, hxp⟩
    have hfulldisjoint : C ∩ ((a ∪ W) ∩ (b \ {p})) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hxC, hxa, hxb, hxp⟩
      have hxa' : x ∈ a := hxa.elim id (fun hxW => hWa ⟨hxW, hxp⟩)
      have hbad : x ∈ (C \ {p}) ∩ (a ∩ b) := ⟨⟨hxC, hxp⟩, hxa', hxb⟩
      simpa only [hdisjoint', Set.mem_empty_iff_false] using hbad
    rcases isPreconnected_iff_subset_of_disjoint.mp hC (a ∪ W) (b \ {p})
        (ha.union hW) (hb.inter isOpen_compl_singleton) hfullcover hfulldisjoint with hall | hall
    · intro x hx
      exact (hall hx.1).elim id (fun hxW => hWa ⟨hxW, hx.2⟩)
    · exact ((hall hpC).2 (Set.mem_singleton p)).elim
  rcases isPreconnected_iff_subset_of_disjoint.mp hpunct u v hu hv
      hlocalcover hlocaldisjoint with hlocal | hlocal
  · exact Or.inl (hside u v hu hv hcover hdisjoint hlocal)
  · exact Or.inr (hside v u hv hu (by rwa [Set.union_comm])
      (by rw [Set.inter_comm v u]; exact hdisjoint) hlocal)



theorem punctured_component_connected (A : GeneralizedSliceCarrier.{u}) (p : A.carrier) :
    IsConnected (connectedComponent p \ {p}) := by
  obtain ⟨B, hcenter, hsub, _⟩ := exists_surgeryBall_in_open A p
    (componentOpen A p).isOpen mem_connectedComponent
  let W : Set A.carrier := B.map '' Metric.ball (0 : StandardCapSpace) 2
  have hpunct : IsConnected (W \ {p}) := by
    simpa only [hcenter] using surgeryBall_punctured_image_connected B
  have hpW : p ∈ W := ⟨0, by simp, hcenter⟩
  have hWC : W ⊆ connectedComponent p := hsub
  exact ⟨hpunct.nonempty.mono (fun x hx => ⟨hWC hx.1, hx.2⟩),
    preconnected_diff_singleton_of_local isConnected_connectedComponent.isPreconnected
      mem_connectedComponent (surgeryBall_image_open B) hpW hWC hpunct.isPreconnected⟩


theorem punctured_component_preconnected (A : GeneralizedSliceCarrier.{u}) (p : A.carrier) :
    IsPreconnected (connectedComponent p \ {p}) :=
  (punctured_component_connected A p).isPreconnected


theorem surgeryBallCollapse_mem_component {x : A.carrier}
    (hx : x ∈ connectedComponent (B.map 0)) (hexterior : x ∈ B.closedBallᶜ) :
    surgeryBallCollapse B x ∈ connectedComponent (B.map 0) := by
  by_cases hu : x ∈ B.map '' Metric.ball (0 : StandardCapSpace) 2
  · obtain ⟨hpos, hupper⟩ := surgeryBall_exterior_coordinates B hexterior hu
    rw [surgeryBallCollapse, surgeryBallPatch_of_mem B _ hu]
    exact surgeryBall_image_subset_center_component B
      ⟨_, punctureCollapse_mem_ball hpos hupper, rfl⟩
  · rw [surgeryBallCollapse, surgeryBallPatch_of_not_mem B _ hu]
    exact hx


theorem surgeryBallExpand_mem_component {x : A.carrier}
    (hx : x ∈ connectedComponent (B.map 0)) (hpuncture : x ∈ ({B.map 0} : Set A.carrier)ᶜ) :
    surgeryBallExpand B x ∈ connectedComponent (B.map 0) := by
  by_cases hu : x ∈ B.map '' Metric.ball (0 : StandardCapSpace) 2
  · obtain ⟨hpos, hupper⟩ := surgeryBall_puncture_coordinates B hpuncture hu
    rw [surgeryBallExpand, surgeryBallPatch_of_mem B _ hu]
    exact surgeryBall_image_subset_center_component B
      ⟨_, punctureExpand_mem_ball hpos hupper, rfl⟩
  · rw [surgeryBallExpand, surgeryBallPatch_of_not_mem B _ hu]
    exact hx



theorem surgeryBall_component_complement_connected :
    IsConnected (connectedComponent (B.map 0) \ B.closedBall) := by
  have himage : surgeryBallExpand B '' (connectedComponent (B.map 0) \ {B.map 0}) =
      connectedComponent (B.map 0) \ B.closedBall := by
    apply Set.Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact ⟨surgeryBallExpand_mem_component B hx.1 hx.2, surgeryBallExpand_mapsTo B hx.2⟩
    · intro y hy
      exact ⟨surgeryBallCollapse B y,
        ⟨surgeryBallCollapse_mem_component B hy.1 hy.2, surgeryBallCollapse_mapsTo B hy.2⟩,
        surgeryBallExpand_collapse B hy.2⟩
  rw [← himage]
  exact (punctured_component_connected A (B.map 0)).image (surgeryBallExpand B)
    ((surgeryBallPunctureEquivalence B).inverse_smooth.continuousOn.mono
      (fun x hx => hx.2))

end PoincareConjecture.M38
