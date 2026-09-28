import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Bigons.ResidualConfinement
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.DiskReplacement
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Disks.SupportedExtension

set_option autoImplicit false
open Set Geometry unitInterval

namespace PoincareConjecture.M76.Dehn

local notation "V" => (ℝ × ℝ)

theorem exists_returning_arc_motion_fixing_residual
    {W B U E : Set V} {a b : V} (hW : IsFinitePLBallPair ℝ W {a, b})
    (hab : a.1 < b.1) (ha : a.2 = 0) (hb : b.2 = 0)
    (hup : ∀ x ∈ W, 0 ≤ x.2) (haxis : W ∩ {x : V | x.2 = 0} = {a, b})
    (hB : IsFinitePLBallPair V B (segment ℝ a b ∪ W))
    (hU : IsOpen U) (hBU : B ⊆ U) (hE : IsClosed E) (hBE : Disjoint B E)
    (T : SimplicialComplex ℝ V) (hT : T.faces.Finite)
    (hlower : ∀ x ∈ T.space, x.2 ≤ 0)
    (hTaxis : ∀ x ∈ T.space, x.2 = 0 → x = a ∨ x = b) :
    ∃ (D : Set V) (H : I → V ≃ₜ V) (F Fi : (ℝ × V) → V),
      IsFinitePLBallPair V D (frontier D) ∧ D ⊆ U ∧
      H 0 = Homeomorph.refl V ∧
      Continuous (fun z : I × V => H z.1 z.2) ∧
      Continuous (fun z : I × V => (H z.1).symm z.2) ∧
      (∀ t : I, ∀ x : V, x ∉ interior D → H t x = x) ∧
      (∀ t : I, ∀ x ∈ T.space ∪ E, H t x = x) ∧
      H 1 '' W = segment ℝ a b ∧
      (∀ t : I, ∀ x : V, F ((t : ℝ), x) = H t x) ∧
      (∀ t : I, ∀ x : V, Fi ((t : ℝ), x) = (H t).symm x) ∧
      ∀ K : SimplicialComplex ℝ V, K.faces.Finite →
        FinitePiecewiseAffineOn F (Icc (0 : ℝ) 1 ×ˢ K.space) ∧
        FinitePiecewiseAffineOn Fi (Icc (0 : ℝ) 1 ×ˢ K.space) := by
  obtain ⟨D, hDcompact, hD, hDU, _, haD, hbD, hWD, hwD, hWi, hwi, _, havoid, hDE⟩ :=
    exists_returning_disk_avoiding_endpoint_and_distant_residual
      hW hab ha hb hup haxis hB hU hBU hE hBE T hT hlower hTaxis
  have hab' : a ≠ b := fun h => hab.ne (congrArg Prod.fst h)
  have hw : IsFinitePLBallPair ℝ (segment ℝ a b) {a, b} := by
    have hh := isFinitePLBallPair_affine_interval zero_lt_one
      (ContinuousAffineMap.lineMap a b) (AffineMap.lineMap_injective ℝ hab').injOn
    simpa only [ContinuousAffineMap.coe_lineMap_eq, AffineMap.lineMap_apply_zero,
      AffineMap.lineMap_apply_one, ← segment_eq_image_lineMap] using hh
  obtain ⟨u, hu, hu0, hu1⟩ := hW.exists_unitInterval_chart_with_endpoints hab'
  obtain ⟨v, hv, hv0, hv1⟩ := hw.exists_unitInterval_chart_with_endpoints hab'
  let q : W ≃ₜ segment ℝ a b := u.symm.trans v
  have hq : q.IsFinitePL := hu.symm.trans hv
  have hends (x : W) (hx : (x : V) ∈ ({a, b} : Set V)) : (q x : V) = x := by
    rcases hx with hx | hx
    · have hxu : x = u 0 := Subtype.ext (hx.trans hu0.symm)
      rw [hxu]
      change (v (u.symm (u 0)) : V) = u 0
      rw [u.symm_apply_apply]
      exact hv0.trans hu0.symm
    · have hxu : x = u 1 := Subtype.ext (hx.trans hu1.symm)
      rw [hxu]
      change (v (u.symm (u 1)) : V) = u 1
      rw [u.symm_apply_apply]
      exact hv1.trans hu1.symm
  obtain ⟨J, hJ, _, hfix, hJq, _⟩ := exists_finitePL_proper_arc_replacement_fix_rim
    hD hW hw haD hbD hab'
    (hWi.trans (hD.interior_eq_sdiff_of_finrank_eq rfl).subset)
    (hwi.trans (hD.interior_eq_sdiff_of_finrank_eq rfl).subset) q hq hends
  obtain ⟨H, F, Fi, hzero, hone, hc, hci, hfixed, hFv, hFiv, hPL⟩ :=
    hD.exists_supported_joint_PL_isotopy J hJ hfix
  have hterminal (x : W) : H 1 x = (q x : V) := by
    rw [hone, J.closedExtension_apply_mem hD.isCompact.isClosed hfix (hWD x.property)]
    exact hJq x (hWD x.property)
  refine ⟨D, H, F, Fi, hD, hDU, hzero, hc, hci, hfixed, ?_, ?_, hFv, hFiv, hPL⟩
  · intro t x hx
    apply hfixed
    intro hi
    rcases hx with hxT | hxE
    · have hxends := havoid ⟨interior_subset hi, hxT⟩
      rcases hxends with hxa | hxb
      · exact haD.2 (hxa ▸ hi)
      · exact hbD.2 (hxb ▸ hi)
    · exact disjoint_left.mp hDE (interior_subset hi) hxE
  · apply Subset.antisymm
    · rintro x ⟨y, hy, rfl⟩
      rw [hterminal ⟨y, hy⟩]
      exact (q ⟨y, hy⟩).property
    · intro x hx
      refine ⟨q.symm ⟨x, hx⟩, (q.symm ⟨x, hx⟩).property, ?_⟩
      rw [hterminal (q.symm ⟨x, hx⟩), q.apply_symm_apply]

end PoincareConjecture.M76.Dehn
