import PoincareConjecture.Proofs.M76.Triangulation.HamiltonZeroCorePointMove
import PoincareConjecture.Proofs.M76.PrimeReduction.BallSupportedAmbientExtension
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalPLMotionComposition
import PoincareConjecture.Proofs.M76.Mathlib.SupportedChartPLTransition
import Mathlib.Topology.Connected.Clopen



set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

private theorem exists_supported_PL_cube_point_move (z : V3) (hz : ‖z‖ < 2) :
    ∃ G : V3 ≃ₜ V3, G.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid V3 ∧
      G 0 = z ∧ EqOn G id (closedBall (0 : V3) 2)ᶜ := by
  obtain ⟨M,hM,hM0,hout⟩ := exists_supported_finitePL_cube_point_move z hz
  have hfix : EqOn M id (closedBall (0 : V3) 2)ᶜ := by
    intro x hx
    apply hout
    exact (lt_of_not_ge (fun h => hx (mem_closedBall_zero_iff.mpr h))).le
  have hMC : M '' closedBall (0 : V3) 2 = closedBall (0 : V3) 2 := by
    apply compl_injective
    rw [←image_compl_eq M.bijective,hfix.image_eq_self]
  let H := (M.image (closedBall (0 : V3) 2)).trans (Homeomorph.setCongr hMC)
  have hH : H.IsFinitePL := ⟨M,hM,fun _ => rfl⟩
  have hHfix : ∀ x : closedBall (0 : V3) 2,
      (x : V3) ∈ frontier (closedBall (0 : V3) 2) → H x = x := by
    intro x hx
    apply Subtype.ext
    apply hout
    rw [frontier_closedBall _ (by norm_num : (2 : ℝ) ≠ 0)] at hx
    exact (mem_sphere_zero_iff_norm.mp hx).ge
  let G := H.closedExtension isClosed_closedBall hHfix
  refine ⟨G,?_,?_,?_⟩
  · apply G.toOpenPartialHomeomorph.mem_piecewiseAffineGroupoid_of_local_finitePL
    intro x _
    obtain ⟨K,hK,hxK,_⟩ := SimplicialComplex.exists_finite_neighborhood_subset_normed
      isCompact_singleton isOpen_univ (singleton_subset_iff.mpr (mem_univ x))
    exact ⟨K.space,hxK (mem_singleton x),
      hH.closedExtension_finite_on_polyhedron isClosed_closedBall hHfix K hK⟩
  · change H.closedExtension isClosed_closedBall hHfix 0 = z
    rw [H.closedExtension_apply_mem isClosed_closedBall hHfix (mem_closedBall_self (by norm_num))]
    exact hM0
  · intro x hx
    exact H.closedExtension_apply_notMem isClosed_closedBall hHfix hx

theorem exists_original_PL_local_point_moves
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3) (p : X) :
    ∃ U : Set X, IsOpen U ∧ p ∈ U ∧ ∀ q ∈ U,
      ∃ (F : X ≃ₜ X) (C : Set X), IsCompact C ∧ EqOn F id Cᶜ ∧ F p = q ∧
        (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
          piecewiseAffineGroupoid V3) ∧
        (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
          piecewiseAffineGroupoid V3) := by
  obtain ⟨i,hpi⟩ := hcover p
  let B := e i
  obtain ⟨ε,hε,hεB⟩ := Metric.isOpen_iff.mp B.open_target (B p) (B.map_source hpi)
  let r := ε / 4
  have hr : 0 < r := by dsimp [r]; positivity
  let A : V3 ≃ᴬ[ℝ] V3 :=
    (LinearEquiv.smulOfNeZero ℝ V3 r hr.ne').toContinuousLinearEquiv.toContinuousAffineEquiv.trans
      (ContinuousAffineEquiv.constVAdd ℝ V3 (B p))
  let Q := B.transHomeomorph A.symm.toHomeomorph
  have hA (z : V3) : A z = B p + r • z := rfl
  have hQp : Q p = 0 := by
    change A.symm (B p) = 0
    apply A.injective
    rw [A.apply_symm_apply,hA,smul_zero,add_zero]
  have hQT : closedBall (0 : V3) 2 ⊆ Q.target := by
    intro z hz
    change A z ∈ B.target
    apply hεB
    rw [mem_ball,dist_eq_norm,hA,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    have hz' := mem_closedBall_zero_iff.mp hz
    have hh : r * ‖z‖ ≤ r * 2 := mul_le_mul_of_nonneg_left hz' hr.le
    have hsmall : r * 2 < ε := by dsimp [r]; linarith
    exact hh.trans_lt hsmall
  have hQ (k : ι) : (e k).symm.trans Q ∈ piecewiseAffineGroupoid V3 := by
    change (e k).symm.trans (B.transHomeomorph A.symm.toHomeomorph) ∈ _
    rw [←OpenPartialHomeomorph.trans_transHomeomorph,
      OpenPartialHomeomorph.transHomeomorph_eq_trans]
    apply (piecewiseAffineGroupoid V3).trans (he k i)
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    exact locallyPiecewiseAffineOn_affine A.symm.toContinuousAffineMap isOpen_univ
  let U := Q.source ∩ Q ⁻¹' ball (0 : V3) 2
  have hU : IsOpen U := Q.isOpen_inter_preimage isOpen_ball
  refine ⟨U,hU,⟨hpi,?_⟩,?_⟩
  · rw [mem_preimage,hQp]
    exact mem_ball_self (by norm_num)
  intro q hq
  obtain ⟨G,hG,hG0,hGfix⟩ := exists_supported_PL_cube_point_move (Q q)
    (mem_ball_zero_iff.mp hq.2)
  obtain ⟨F,hFQ,hFout⟩ := Q.symm.exists_supported_chart_homeomorph G
    (isCompact_closedBall _ _) hQT hGfix
  have hforward (k l : ι) : (e k).symm.trans (F.toOpenPartialHomeomorph.trans (e l)) ∈
      piecewiseAffineGroupoid V3 :=
    Q.symm.supported_chart_transition_mem_piecewiseAffineGroupoid (e k).symm (e l).symm
      G F (isCompact_closedBall _ _) hQT hGfix hFQ hFout hG (hQ k) (hQ l) (he k l)
  refine ⟨F,Q.symm '' closedBall (0 : V3) 2,
    (isCompact_closedBall _ _).image_of_continuousOn (Q.symm.continuousOn.mono hQT),
    hFout,?_,hforward,?_⟩
  · have hv := hFQ (show p ∈ Q.symm.target from hpi)
    change F p = Q.symm (G (Q p)) at hv
    rw [hQp,hG0,Q.left_inv hq.1] at hv
    exact hv
  · intro k l
    simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm,OpenPartialHomeomorph.trans_assoc,
      Homeomorph.symm_toOpenPartialHomeomorph] using
      (piecewiseAffineGroupoid V3).symm (hforward l k)

theorem exists_original_PL_point_motion
    {X ι : Type*} [TopologicalSpace X] [T2Space X] [PreconnectedSpace X]
    (e : ι → OpenPartialHomeomorph X V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3) (p q : X) :
    ∃ (F : X ≃ₜ X) (C : Set X), IsCompact C ∧ EqOn F id Cᶜ ∧ F p = q ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) := by
  let Rel (x y : X) : Prop := ∃ (F : X ≃ₜ X) (C : Set X),
    IsCompact C ∧ EqOn F id Cᶜ ∧ F x = y ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3)
  have htrans {x y z : X} (hxy : Rel x y) (hyz : Rel y z) : Rel x z := by
    obtain ⟨F,C,hC,hfix,hxy,hF,hFi⟩ := hxy
    obtain ⟨G,D,hD,hgfix,hyz,hG,hGi⟩ := hyz
    refine ⟨F.trans G,C ∪ D,hC.union hD,?_,?_,
      original_PL_motion_trans e hcover F G hF hG,
      original_PL_motion_trans e hcover G.symm F.symm hGi hFi⟩
    · intro w hw
      change G (F w) = w
      rw [hfix (fun h => hw (Or.inl h))]
      exact hgfix (fun h => hw (Or.inr h))
    · change G (F x) = z
      rw [hxy,hyz]
  have hsymm {x y : X} (hxy : Rel x y) : Rel y x := by
    obtain ⟨F,C,hC,hfix,hxy,hF,hFi⟩ := hxy
    refine ⟨F.symm,C,hC,?_,?_,hFi,hF⟩
    · intro w hw
      apply F.injective
      change F (F.symm w) = F w
      rw [F.apply_symm_apply]
      exact (hfix hw).symm
    · rw [←hxy,F.symm_apply_apply]
  have hlocal (x : X) : ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, Rel x y :=
    exists_original_PL_local_point_moves e hcover he x
  let A : Set X := {x | Rel p x}
  have hA : IsOpen A := by
    apply isOpen_iff_forall_mem_open.mpr
    intro x hx
    obtain ⟨U,hU,hxU,hmove⟩ := hlocal x
    exact ⟨U,fun y hy => htrans hx (hmove y hy),hU,hxU⟩
  have hAc : IsOpen Aᶜ := by
    apply isOpen_iff_forall_mem_open.mpr
    intro x hx
    obtain ⟨U,hU,hxU,hmove⟩ := hlocal x
    exact ⟨U,fun y hy hyA => hx (htrans hyA (hsymm (hmove y hy))),hU,hxU⟩
  have hpA : p ∈ A := by
    obtain ⟨U,_,hpU,hmove⟩ := hlocal p
    exact hmove p hpU
  have hAU : A = univ := (show IsClopen A from ⟨isOpen_compl_iff.mp hAc,hA⟩).eq_univ ⟨p,hpA⟩
  have hqA : q ∈ A := hAU.symm ▸ mem_univ q
  exact hqA

end PoincareConjecture.M76
