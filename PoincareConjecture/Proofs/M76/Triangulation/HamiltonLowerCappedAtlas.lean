import PoincareConjecture.Proofs.M76.Triangulation.HamiltonLowerOriginalBrownCap
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonCappedAtlas
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedGeometricInputs

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]

local notation "V" => ((ι → ℝ) × (κ → ℝ))
local notation "W" => LatticeHandleAmbient ι κ (hamiltonLowerPeriodLattice κ)
local notation "V3" => (Fin 3 → ℝ)

theorem HamiltonLowerLatticeImmersion.exists_capped_original_PL_domain
    (I : HamiltonLowerLatticeImmersion κ)
    (hdim : Fintype.card ι + Fintype.card κ = 3)
    (h : OpenPartialHomeomorph V V3)
    (hsource : closedBall (0 : ι → ℝ) 1 ×ˢ (univ : Set (κ → ℝ)) ⊆ h.source)
    {N : Set V} (hN : IsOpen N)
    (hboundary : sphere (0 : ι → ℝ) 1 ×ˢ (univ : Set (κ → ℝ)) ⊆ N)
    (hPL : LocallyPiecewiseAffineOn h (h.source ∩ N))
    (wall : ∀ (U : TopologicalSpace.Opens W)
      (charts : Set (OpenPartialHomeomorph U V3)),
      HasWallCompactCore (fun c : charts => (c : OpenPartialHomeomorph U V3)))
    (brown : HasBrownLocallyFlatSphereBalls) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∃ (d : V → OpenPartialHomeomorph W V3)
        (charts : Set (OpenPartialHomeomorph W V3)),
        StandardLatticeHandleAtlas ι κ (hamiltonLowerPeriodLattice κ) d ∧
        PLDomain (fun c : charts => (c : OpenPartialHomeomorph W V3))
          (latticeHandleDomain ι κ (hamiltonLowerPeriodLattice κ)) ∧
        Nonempty (HamiltonRetainedBlockChart ι κ (hamiltonLowerPeriodLattice κ)
          (fun c : charts => (c : OpenPartialHomeomorph W V3)) h) ∧
        ∀ l, (d l).restrOpen {x : W | r < ‖x.1‖}
          (isOpen_lt continuous_const continuous_fst.norm) ∈ charts := by
  classical
  obtain ⟨a, b, ha, ha1, hb, U, hUeq, hU, d, oldCharts, c, K, S, c0, D,
    hd, he, hc, hK, hKR, heK, hSint, hs, hdis, hfrontK, hrelative,
    hretain, hcore, hcollar, hc0, hDdef, hD, hDint, hfrontD, hDc0,
    hDlocal, hcover, hmeet, hball⟩ :=
    I.exists_original_marked_brown_cap hdim h hsource hN hboundary hPL wall brown
  let : Nonempty U := hU
  let H := latticeHandleDomain ι κ (hamiltonLowerPeriodLattice κ)
  let R : Set U := (Subtype.val : U → W) ⁻¹' H
  let e : oldCharts → OpenPartialHomeomorph U V3 := fun i => i
  have hDnorm (x : W) (hx : x ∈ D) : ‖x.1‖ < 1 := by
    have hi := hDint hx
    rw [latticeHandleDomain, interior_prod_eq, interior_univ,
      interior_closedBall _ one_ne_zero] at hi
    exact mem_ball_zero_iff.mp hi.1
  obtain ⟨phi, _⟩ := hball.2
  let xD : D := phi.symm ⟨0, mem_closedBall_self zero_le_one⟩
  obtain ⟨xmax, hxmax, hmax⟩ := hD.exists_isMaxOn
    ⟨xD, xD.property⟩ continuous_fst.norm.continuousOn
  obtain ⟨r, hr, hr1⟩ := exists_between (max_lt ha1 (hDnorm xmax hxmax))
  have har : a < r := (le_max_left _ _).trans_lt hr
  have hr0 : 0 < r := ha.trans har
  let Vcap : Set W := {x | ‖x.1‖ < r}
  let O : Set W := {x | r < ‖x.1‖}
  have hVcap : IsOpen Vcap := isOpen_lt continuous_fst.norm continuous_const
  have hO : IsOpen O := isOpen_lt continuous_const continuous_fst.norm
  have hDV : D ⊆ Vcap := by
    intro x hx
    exact (hmax hx).trans_lt ((le_max_right _ _).trans_lt hr)
  have hVO : Disjoint Vcap O := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    change ‖x.1‖ < r at hx
    change r < ‖x.1‖ at hy
    exact lt_asymm hx hy
  have hfrontHO : frontier H ⊆ O := by
    intro x hx
    have hf : frontier H = sphere (0 : ι → ℝ) 1 ×ˢ univ := by
      simp only [H, latticeHandleDomain, frontier_prod_univ_eq, frontier_closedBall _ one_ne_zero]
    have hn : ‖x.1‖ = 1 := by
      simpa only [mem_sphere, dist_zero_right] using (hf.subset hx).1
    change r < ‖x.1‖
    rw [hn]
    exact hr1
  have houter : Hᶜ ⊆ O := by
    intro x hx
    have hn : 1 < ‖x.1‖ := lt_of_not_ge (fun hn =>
      hx ⟨mem_closedBall_zero_iff.mpr hn, mem_univ _⟩)
    exact hr1.trans hn
  have holdCover : H \ D ⊆ (U : Set W) := by
    rintro x ⟨hxH, hxD⟩
    by_contra hxU
    apply hxD
    rw [hDdef]
    refine ⟨hxH, ?_⟩
    rintro ⟨y, _, rfl⟩
    exact hxU y.property
  let j : OpenPartialHomeomorph U W :=
    U.isOpen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : U → W)
  have hjs : j.source = univ := rfl
  have hj (y : U) : y ∈ j.source := by rw [hjs]; exact mem_univ y
  let B : Set U := {z | a < ‖(z : W).1‖ ∧ ‖(z : W).1‖ < b}
  have hB : IsOpen B :=
    (isOpen_lt continuous_const (continuous_fst.comp continuous_subtype_val).norm).inter
      (isOpen_lt (continuous_fst.comp continuous_subtype_val).norm continuous_const)
  have hcross (i : oldCharts) (l : V) :
      (j.symm.trans (e i)).symm.trans ((d l).restrOpen O hO) ∈
        piecewiseAffineGroupoid V3 := by
    let dU := ((d l).subtypeRestr hU).restr B
    have hT : (e i).symm.trans dU ∈ piecewiseAffineGroupoid V3 := by
      simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.symm_symm] using
          (piecewiseAffineGroupoid V3).symm (hcollar i l)
    let T := (j.symm.trans (e i)).symm.trans ((d l).restrOpen O hO)
    have hsub : T.source ⊆ ((e i).symm.trans dU).source := by
      intro p hp
      refine ⟨hp.1.1, ?_⟩
      rw [OpenPartialHomeomorph.restr_source' _ _ hB]
      refine ⟨?_, ?_⟩
      · rw [OpenPartialHomeomorph.subtypeRestr_source]
        exact hp.2.1
      · have hu := ((e i).symm p).property
        change ((e i).symm p : W) ∈ (U : Set W) at hu
        rw [hUeq] at hu
        have hupper : ‖((e i).symm p : W).1‖ < b := by
          rcases hu with hu | hu
          · exact mem_ball_zero_iff.mp hu.1
          · exact hu.1.2
        have hlower : r < ‖((e i).symm p : W).1‖ := hp.2.2
        exact ⟨har.trans hlower, hupper⟩
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    apply (((mem_piecewiseAffineGroupoid_iff_forward _).mp hT).mono T.open_source hsub).congr
    intro p _
    rfl
  obtain ⟨s⟩ := hs
  have hSK : S ⊆ frontier K := fun _ hy => hfrontK.symm.subset (Or.inr hy)
  obtain ⟨charts, hcharts, hinsert, hstandard⟩ :=
    exists_marked_brown_cap_PL_domain U.isOpen e heK s d hd.domain hD.isClosed hfrontD
      hSK isOpen_interior hSint hDlocal hball hVcap hO hDV hVO hfrontHO
      holdCover houter hcross
  let cnew := (j.symm.trans c).restrOpen Dᶜ hD.isClosed.isOpen_compl
  have hcnew : cnew ∈ charts := hinsert ⟨c, hc⟩
  have hnewcore (x : V) (hx : x ∈ closedBall (0 : ι → ℝ) 1 ×ˢ
      closedBall (0 : κ → ℝ) 2) :
      hamiltonMarkedProjection ι κ (hamiltonLowerPeriodLattice κ) x ∈ cnew.source ∧
      cnew (hamiltonMarkedProjection ι κ (hamiltonLowerPeriodLattice κ) x) = h x := by
    obtain ⟨z, hzR, hzpi, hzc, hzval, hzint⟩ := hcore x hx
    have hznot : (z : W) ∉ D := by
      intro hzD
      rw [hDdef] at hzD
      exact hzD.2 ⟨z, ⟨(⟨z, hzR⟩ : R), hzint, rfl⟩, rfl⟩
    have hznew : (z : W) ∈ cnew.source := by
      refine ⟨⟨j.map_source (hj z), ?_⟩, hznot⟩
      change j.symm (j z) ∈ c.source
      rw [j.left_inv (hj z)]
      exact hzc
    have hznewval : cnew (z : W) = h x := by
      change c (j.symm (j z)) = h x
      rw [j.left_inv (hj z)]
      exact hzval
    change (x.1, QuotientAddGroup.mk x.2) ∈ cnew.source ∧
      cnew (x.1, QuotientAddGroup.mk x.2) = h x
    rw [← hzpi]
    exact ⟨hznew, hznewval⟩
  have hquot : InjOn (hamiltonMarkedProjection ι κ (hamiltonLowerPeriodLattice κ))
      (closedBall (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) 2) := by
    intro x hx y hy hxy
    have hx3 : ‖x.2‖ ≤ 3 := (mem_closedBall_zero_iff.mp hx.2).trans (by norm_num)
    have hy3 : ‖y.2‖ ≤ 3 := (mem_closedBall_zero_iff.mp hy.2).trans (by norm_num)
    apply Prod.ext
    · have hfst := congrArg Prod.fst hxy
      change x.1 = y.1 at hfst
      exact hfst
    · exact (I.core x.2 hx3).2.symm.trans
        ((congrArg I.map (congrArg Prod.snd hxy)).trans (I.core y.2 hy3).2)
  let retained : HamiltonRetainedBlockChart ι κ (hamiltonLowerPeriodLattice κ)
      (fun c : charts => (c : OpenPartialHomeomorph W V3)) h := {
    quotient_injective := hquot
    index := ⟨cnew, hcnew⟩
    contains := fun x hx => (hnewcore x hx).1
    formula := fun x hx => (hnewcore x hx).2 }
  exact ⟨r, hr0, hr1, d, charts, hd, hcharts, ⟨retained⟩, hstandard⟩

end PoincareConjecture.M76
