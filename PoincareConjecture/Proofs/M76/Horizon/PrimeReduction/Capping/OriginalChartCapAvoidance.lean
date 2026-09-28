import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.CoordinateBallCompression
import PoincareConjecture.Proofs.M76.Mathlib.SupportedChartPLTransition
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalPointPosition
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalPLMotionComposition
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.Topology
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas









set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_chart_cap_avoidance_of_center_clear
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S A : Set X}
    (hS : IsClosed S) (hA : IsCompact A)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (Q : OpenPartialHomeomorph X V3) (hQT : Q.target = ball (0 : V3) 1)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (hAQ : A ⊆ Q.source) (hcenter : Q.symm 0 ∉ S) :
    ∃ (F : X ≃ₜ X) (C : Set X),
      IsCompact C ∧ C ⊆ Q.source ∧ EqOn F id Cᶜ ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧ Disjoint (F '' S) A := by
  have h0 : (0 : V3) ∈ Q.target := hQT.symm ▸ mem_ball_self zero_lt_one
  have hAc : IsCompact (Q '' A) := hA.image_of_continuousOn (Q.continuousOn.mono hAQ)
  have hAunit : Q '' A ⊆ ball (0 : V3) 1 := by
    rintro _ ⟨x,hx,rfl⟩
    exact hQT ▸ Q.map_source (hAQ hx)
  obtain ⟨a,⟨ha,ha1⟩,hAa⟩ := exists_pos_lt_subset_ball zero_lt_one hAc.isClosed hAunit
  let b := (a+1)/2
  have hab : a < b := by dsimp [b]; linarith
  have hb1 : b < 1 := by dsimp [b]; linarith
  have hb : 0 < b := ha.trans hab
  let V := Q '' (Q.source ∩ Sᶜ)
  have hV : IsOpen V := Q.isOpen_image_of_subset_source
    (Q.open_source.inter hS.isOpen_compl) inter_subset_left
  have h0V : (0 : V3) ∈ V :=
    ⟨Q.symm 0,⟨Q.map_target h0,hcenter⟩,Q.right_inv h0⟩
  obtain ⟨ε,hε,hεV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds h0V)
  let c := min ε b / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hcε : c < ε := by dsimp [c]; have := min_le_left ε b; linarith
  have hcb : c < b := by dsimp [c]; have := min_le_right ε b; linarith
  have hsmallV : closedBall (0 : V3) c ⊆ V :=
    (closedBall_subset_ball hcε).trans hεV
  obtain ⟨G,hGPL,hGout,_,hGmem⟩ := exists_supported_coordinate_ball_compression ha hab hc hcb
  have hGfix : EqOn G.symm id (closedBall (0 : V3) b)ᶜ := by
    intro x hx
    have hxb : b ≤ ‖x‖ := (show b < ‖x‖ from by
      simpa only [mem_compl_iff,mem_closedBall,dist_zero_right,not_le] using hx).le
    change G.symm x = x
    apply G.injective
    rw [G.apply_symm_apply,hGout x hxb]
  have hbt : closedBall (0 : V3) b ⊆ Q.target := by
    rw [hQT]
    exact closedBall_subset_ball hb1
  obtain ⟨F,hFQ,hFout⟩ := Q.symm.exists_supported_chart_homeomorph G.symm
    (isCompact_closedBall _ _) hbt hGfix
  have hforward (i j : ι) :
      (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈ piecewiseAffineGroupoid V3 :=
    Q.symm.supported_chart_transition_mem_piecewiseAffineGroupoid (e i).symm (e j).symm
      G.symm F (isCompact_closedBall _ _) hbt hGfix hFQ hFout
      ((piecewiseAffineGroupoid V3).symm hGPL) (hQ i) (hQ j) (he i j)
  refine ⟨F,Q.symm '' closedBall (0 : V3) b,
    (isCompact_closedBall _ _).image_of_continuousOn (Q.symm.continuousOn.mono hbt),
    fun _ hx => by obtain ⟨z,hz,rfl⟩ := hx; exact Q.map_target (hbt hz),
    hFout,hforward,?_,?_⟩
  · intro i j
    have hinv := (piecewiseAffineGroupoid V3).symm (hforward j i)
    simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm,OpenPartialHomeomorph.trans_assoc,
      Homeomorph.symm_toOpenPartialHomeomorph] using hinv
  · apply disjoint_left.mpr
    rintro y ⟨x,hx,hxy⟩ hy
    have hyQ := hAQ hy
    have hya : ‖Q y‖ ≤ a := (mem_ball_zero_iff.mp (hAa ⟨y,hy,rfl⟩)).le
    have hGy : G (Q y) ∈ closedBall (0 : V3) c :=
      mem_closedBall_zero_iff.mpr ((hGmem (Q y)).mp hya)
    obtain ⟨z,⟨hzQ,hzS⟩,hz⟩ := hsmallV hGy
    have hQz : Q z = G (Q y) := hz
    have hFz : F z = y := by
      have hv := hFQ hzQ
      change F z = Q.symm (G.symm (Q z)) at hv
      rw [hQz,G.symm_apply_apply,Q.left_inv hyQ] at hv
      exact hv
    exact hzS (F.injective (hxy.trans hFz.symm) ▸ hx)

theorem ChartwisePLSphere.exists_motion_avoiding_compact_in_ball_chart
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S A : Set X}
    (s : ChartwisePLSphere e S) (hA : IsCompact A)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (Q : OpenPartialHomeomorph X V3) (hQT : Q.target = ball (0 : V3) 1)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (hAQ : A ⊆ Q.source) :
    ∃ (F : X ≃ₜ X) (C : Set X),
      IsCompact C ∧ C ⊆ Q.source ∧ EqOn F id Cᶜ ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      Nonempty (ChartwisePLSphere e (F '' S)) ∧ Disjoint (F '' S) A := by
  have h0 : (0 : V3) ∈ Q.target := hQT.symm ▸ mem_ball_self zero_lt_one
  obtain ⟨P,C₁,hC₁,hC₁Q,hPfix,hPPL,hPinv,⟨sP⟩,hcenter⟩ :=
    s.exists_point_avoiding_motion hcover he Q.open_source (Q.map_target h0)
  obtain ⟨G,C₂,hC₂,hC₂Q,hGfix,hGPL,hGinv,hGA⟩ :=
    exists_original_chart_cap_avoidance_of_center_clear sP.isCompact.isClosed hA he Q hQT hQ hAQ hcenter
  have hforward := original_PL_motion_trans e hcover P G hPPL hGPL
  refine ⟨P.trans G,C₁ ∪ C₂,hC₁.union hC₂,union_subset hC₁Q hC₂Q,?_,hforward,
    original_PL_motion_trans e hcover G.symm P.symm hGinv hPinv,
    s.nonempty_image (P.trans G) hcover hforward,?_⟩
  · intro x hx
    change G (P x) = x
    rw [hPfix (fun h => hx (Or.inl h))]
    exact hGfix (fun h => hx (Or.inr h))
  · rw [image_image] at hGA
    exact hGA

end PoincareConjecture.M76
