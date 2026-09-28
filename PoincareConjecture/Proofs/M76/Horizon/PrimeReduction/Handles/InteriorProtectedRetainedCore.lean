import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.OriginalPLPointMotion
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.OriginalFiniteCapAvoidance
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedGeometricInputs
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonMarkedApproximation

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem ChartwisePLBall.exists_original_PL_motion_into_open
    {X ι : Type*} [MetricSpace X] [PreconnectedSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {D B R U : Set X}
    (b : ChartwisePLBall e D B) (hR : IsCompact R) (he : PLDomain e R)
    (hDR : D ⊆ interior R) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ (F : X ≃ₜ X) (C : Set X), IsCompact C ∧ EqOn F id Cᶜ ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧ MapsTo F D U := by
  obtain ⟨Q,hDQ,_,hQT,hQ⟩ :=
    b.exists_enclosing_chart_in_domain hR he hDR isOpen_univ (subset_univ D)
  obtain ⟨q,hq⟩ := hUne
  obtain ⟨P,C₁,hC₁,hPfix,hPp,hP,hPi⟩ :=
    exists_original_PL_point_motion e he.cover he.compatible (Q.symm 0) q
  let S := (P ⁻¹' U)ᶜ
  have hS : IsClosed S := (hU.preimage P.continuous).isClosed_compl
  have hcenter : Q.symm 0 ∉ S := by
    change ¬P (Q.symm 0) ∉ U
    rw [hPp]
    exact not_not.mpr hq
  obtain ⟨G,C₂,hC₂,_,hGfix,hG,hGi,hclear⟩ :=
    exists_original_chart_cap_avoidance_of_center_clear hS b.isCompact he.compatible
      Q hQT hQ hDQ hcenter
  have hGifix : EqOn G.symm id C₂ᶜ := by
    intro x hx
    apply G.injective
    change G (G.symm x) = G x
    rw [G.apply_symm_apply]
    exact (hGfix hx).symm
  refine ⟨G.symm.trans P,C₂ ∪ C₁,hC₂.union hC₁,?_,
    original_PL_motion_trans e he.cover G.symm P hGi hP,
    original_PL_motion_trans e he.cover P.symm G hPi hG,?_⟩
  · intro x hx
    change P (G.symm x) = x
    rw [hGifix (fun h => hx (Or.inl h))]
    exact hPfix (fun h => hx (Or.inr h))
  · intro x hx
    have hnot : G.symm x ∉ S := by
      intro h
      exact disjoint_left.mp hclear ⟨G.symm x,h,G.apply_symm_apply x⟩ hx
    exact not_not.mp hnot

theorem exists_zero_lattice_protected_ball_placement
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    (hindex : Fintype.card ι = 0) (he : PLDomain e (latticeHandleDomain ι κ L))
    {D U : Set (LatticeHandleAmbient ι κ L)}
    (bD : HamiltonMarkedProtectedBall ι κ L e D) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ (F : LatticeHandleAmbient ι κ L ≃ₜ LatticeHandleAmbient ι κ L)
      (C : Set (LatticeHandleAmbient ι κ L)), IsCompact C ∧ EqOn F id Cᶜ ∧
      F '' latticeHandleDomain ι κ L = latticeHandleDomain ι κ L ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧ MapsTo F D U := by
  let : IsEmpty ι := Fintype.card_eq_zero_iff.mp hindex
  have hquot : IsConnected (univ : Set ((κ → ℝ) ⧸ L.toAddSubgroup)) := by
    have h := (isConnected_univ : IsConnected (univ : Set (κ → ℝ))).image
      (QuotientAddGroup.mk : (κ → ℝ) → ((κ → ℝ) ⧸ L.toAddSubgroup))
      QuotientAddGroup.continuous_mk.continuousOn
    simpa only [image_univ,range_eq_univ.mpr QuotientAddGroup.mk_surjective] using h
  let : PreconnectedSpace (LatticeHandleAmbient ι κ L) := ⟨by
    simpa only [univ_prod_univ] using
      (isConnected_univ : IsConnected (univ : Set (ι → ℝ))).prod hquot |>.isPreconnected⟩
  have hR : latticeHandleDomain ι κ L = univ := by
    ext x
    have hx : x.1 = 0 := Subsingleton.elim _ _
    simp [latticeHandleDomain,hx]
  have hDR : D ⊆ interior (latticeHandleDomain ι κ L) := by
    rw [hR,interior_univ]
    exact subset_univ D
  obtain ⟨F,C,hC,hfix,hF,hFi,hFD⟩ := bD.ball.exists_original_PL_motion_into_open
    (isCompact_latticeHandleDomain ι κ L) he hDR hU hUne
  refine ⟨F,C,hC,hfix,?_,hF,hFi,hFD⟩
  rw [hR,image_univ,F.surjective.range_eq]

end PoincareConjecture.M76
