import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.CapSlice.Region
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.CapSlice.Tube
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.DiskComplement

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

variable {v : E3} {g : S2 → E3} {B : Set Real}

theorem exists_truncated_cap_disks (D : SphereSurgeryCoreCap v g B)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    {a : Real} (ha : 0 < a) (ha1 : a < 1) :
    ∃ ε : Real, 0 < ε ∧ ε < a ∧ ε < 1-a ∧
      ∃ (J : Hemisphere.Plane v ≃ₗᵢ[Real] E2)
        (T : OpenPartialHomeomorph (S1 × Real) S2),
        T.source = univ ×ˢ Ioo (-ε) ε ∧
        ContMDiffOn Iprod (𝓡 2) ∞ T T.source ∧
        ContMDiffOn (𝓡 2) Iprod ∞ T.symm T.target ∧
        (∀ q t, t ∈ Ioo (-ε) ε →
          g (T (q, t)) = (D.center+D.scale*(a+t)) • v +
            (D.planeMap (J.symm (q : E2)) : E3)) ∧
        ∃ d e : OpenPartialHomeomorph E2 S2,
          closedBall 0 1 ⊆ d.source ∧ closedBall 0 1 ⊆ e.source ∧
          ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source ∧
          ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target ∧
          ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
          ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
          d '' closedBall 0 1 = (D.chart '' closedBall (0 : E2) 1) ∩
            {p : S2 | a ≤ (inner Real v (g p)-D.center)/D.scale} ∧
          d '' ball 0 1 = (D.chart '' closedBall (0 : E2) 1) ∩
            {p : S2 | a < (inner Real v (g p)-D.center)/D.scale} ∧
          e '' closedBall 0 1 = (d '' ball 0 1)ᶜ ∧
          e '' ball 0 1 = (d '' closedBall 0 1)ᶜ ∧
          range (fun q : S1 => T (q, 0)) = d '' sphere (0 : E2) 1 ∧
          range (fun q : S1 => T (q, 0)) = e '' sphere (0 : E2) 1 ∧
          (∀ q t, t ∈ Ioo (-ε) 0 → T (q, t) ∈ e '' ball 0 1) ∧
          (∀ q t, t ∈ Ioo 0 ε → T (q, t) ∈ d '' ball 0 1) := by
  let ε := min a (1-a)/2
  have hε : 0 < ε := half_pos (lt_min ha (by linarith))
  have hεa : ε < a := by dsimp [ε]; linarith [min_le_left a (1-a)]
  have hε1 : ε < 1-a := by dsimp [ε]; linarith [min_le_right a (1-a)]
  obtain ⟨J, T, hTs, hT, hTi, hformula, hTin, hcenter⟩ :=
    D.exists_normalized_belt_chart hg hε hεa hε1
  let H : S2 → Real := fun p => (inner Real v (g p)-D.center)/D.scale
  let K : Set S2 := (D.chart '' closedBall (0 : E2) 1) ∩ {p | a ≤ H p}
  have hH : Continuous H :=
    (((innerSL Real v).continuous.comp hg.contMDiff.continuous).sub continuous_const).div_const D.scale
  have hD : IsClosed (D.chart '' closedBall (0 : E2) 1) :=
    ((isCompact_closedBall 0 1).image_of_continuousOn
      (D.chart.continuousOn.mono D.source)).isClosed
  have hK : IsClosed K := hD.inter (isClosed_le continuous_const hH)
  have hstrict (p : S2) (hpD : p ∈ D.chart '' closedBall (0 : E2) 1)
      (hp : a < H p) : p ∈ interior K := by
    have hpopen : p ∈ D.chart '' ball (0 : E2) 1 := by
      obtain ⟨x, hx, rfl⟩ := hpD
      refine ⟨x, mem_ball_zero_iff.mpr ?_, rfl⟩
      apply lt_of_le_of_ne (mem_closedBall_zero_iff.mp hx)
      intro heq
      have hh : H (D.chart x) = 0 := by
        dsimp [H]
        rw [D.parametrization_eq x hx,
          D.boundary_height x (mem_sphere_zero_iff_norm.mpr heq), sub_self, zero_div]
      rw [hh] at hp
      linarith
    have hopen : IsOpen ((D.chart '' ball (0 : E2) 1) ∩ {p | a < H p}) :=
      (D.chart.isOpen_image_of_subset_source isOpen_ball
        (ball_subset_closedBall.trans D.source)).inter (isOpen_lt continuous_const hH)
    have hsub : (D.chart '' ball (0 : E2) 1) ∩ {p | a < H p} ⊆ K :=
      fun q hq => ⟨image_mono ball_subset_closedBall hq.1, le_of_lt (show a < H q from hq.2)⟩
    exact interior_maximal hsub hopen ⟨hpopen, hp⟩
  have hproper : K ≠ univ := by
    obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (E := E2)).mpr
      (show (0 : Real) ≤ 1 by norm_num)
    intro heq
    have hh : a ≤ H (D.chart x) := (heq.symm ▸ mem_univ (D.chart x)).2
    dsimp [H] at hh
    rw [D.parametrization_eq x (sphere_subset_closedBall hx), D.boundary_height x hx,
      sub_self, zero_div] at hh
    linarith
  have hfront : frontier K ⊆ range (fun q : S1 => T (q, 0)) := by
    intro p hp
    have hpK := hK.frontier_subset hp
    rw [hcenter]
    refine ⟨hpK.1, le_antisymm ?_ hpK.2⟩
    by_contra hh
    exact hp.2 (hstrict p hpK.1 (lt_of_not_ge hh))
  have hHt (q : S1) (t : Real) (ht : t ∈ Ioo (-ε) ε) : H (T (q,t)) = a+t := by
    dsimp [H]
    rw [hformula q t ht]
    have hh : inner Real v ((D.center+D.scale*(a+t)) • v +
        (D.planeMap (J.symm (q : E2)) : E3)) = D.center+D.scale*(a+t) := by
      simpa only [Poincare.Geometry.Euclidean.heightCoordinates_apply] using
        Poincare.Geometry.Euclidean.inner_heightCoordinates D.unit_v
          (D.center+D.scale*(a+t), D.planeMap (J.symm (q : E2)))
    rw [hh, add_sub_cancel_left, mul_div_cancel_left₀ (a+t) D.scale_ne_zero]
  have hne : (interior K \ range (fun q : S1 => T (q,0))).Nonempty := by
    obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (E := E2)).mpr
      (show (0 : Real) ≤ 1 by norm_num)
    let q : S1 := ⟨x,hx⟩
    have ht : ε/2 ∈ Ioo (-ε) ε := ⟨by linarith, by linarith⟩
    refine ⟨T (q,ε/2), hstrict _ (image_mono ball_subset_closedBall (hTin q _ ht)) ?_, ?_⟩
    · rw [hHt q _ ht]
      linarith
    · rw [hcenter]
      intro hh
      have heq : H (T (q,ε/2)) = a := hh.2
      rw [hHt q _ ht] at heq
      linarith
  obtain ⟨hC, hCi, hCd⟩ := central_circle_geometry_of_tube hε T hT hTi hTs
  obtain ⟨d, hds, hd, hdi, hdc, hdb⟩ :=
    exists_disk_neighborhood_of_frontier_subset_circle hC hCi hCd hK hproper hfront hne
  have hdo : d '' ball 0 1 = (D.chart '' closedBall (0 : E2) 1) ∩ {p | a < H p} := by
    rw [d.image_ball_eq_interior hds hdc]
    apply Subset.antisymm
    · intro p hp
      have hpK := interior_subset hp
      refine ⟨hpK.1, ?_⟩
      change a < H p
      apply lt_of_le_of_ne hpK.2
      intro heq
      have hpboundary : p ∈ frontier K := by
        rw [← d.image_sphere_eq_frontier hds hdc, hdb, hcenter]
        exact ⟨hpK.1, heq.symm⟩
      exact hpboundary.2 hp
    · exact fun p hp => hstrict p hp.1 hp.2
  let Q : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 S2 ∞ :=
    { d with contMDiffOn_toFun := hd, contMDiffOn_invFun := hdi }
  obtain ⟨R, E, hR, hEs, hE, hEi, hEc⟩ := exists_complementary_disk_neighborhood
    zero_lt_one d (d.injOn.mono hds)
      (fun x hx => Q.isLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ (hds hx))
  obtain ⟨e, hes, he, hei, hec, _, _⟩ :=
    ParallelDisks.exists_rescaled_disk_chart hR E hEs hE hEi
  have heclosed : e '' closedBall 0 1 = (d '' ball 0 1)ᶜ := hec.trans hEc
  have heopen : e '' ball 0 1 = (d '' closedBall 0 1)ᶜ := by
    rw [e.image_ball_eq_interior hes heclosed, interior_compl,
      ParallelDisks.closure_image_ball zero_lt_one d hds]
  have heboundary : e '' sphere (0 : E2) 1 = range (fun q : S1 => T (q,0)) := by
    rw [e.image_sphere_eq_frontier hes heclosed, frontier_compl,
      ParallelDisks.frontier_image_ball zero_lt_one d hds hd hdi, hdb]
  refine ⟨ε, hε, hεa, hε1, J, T, hTs, hT, hTi, hformula,
    d, e, hds, hes, hd, hdi, he, hei, hdc, hdo, heclosed, heopen,
    hdb.symm, heboundary.symm, ?_, ?_⟩
  · intro q t ht
    rw [heopen, hdc]
    intro hp
    have hh : a ≤ H (T (q,t)) := hp.2
    rw [hHt q t ⟨ht.1, ht.2.trans hε⟩] at hh
    linarith [ht.2]
  · intro q t ht
    rw [hdo]
    have ht' : t ∈ Ioo (-ε) ε := ⟨by linarith [ht.1], ht.2⟩
    refine ⟨image_mono ball_subset_closedBall (hTin q t ht'), ?_⟩
    change a < H (T (q,t))
    rw [hHt q t ht']
    linarith [ht.1]

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap
