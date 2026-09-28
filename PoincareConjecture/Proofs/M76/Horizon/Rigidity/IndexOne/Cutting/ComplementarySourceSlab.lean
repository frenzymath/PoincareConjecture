import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.ShiftedCircleSlabDomain
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.RelativeEndpointChart
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.MarkedRimCharts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.SourceSlab
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Arcs.ComplementarySlabContraction
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.SourceSurface

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

private instance : Fact (0 < p) := ⟨by norm_num⟩

theorem exists_complementary_sourceSlabs_with_transverse_corners
    {α β : Type*} (e : α → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3)
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (F : (ContinuousMap.id H).HomotopyRel phi B) :
    ∃ a ∈ Ioo (p / 4) (p / 3), ∃ b ∈ Ioo (2 * p / 3) (3 * p / 4),
      IsCompact (sourceSlab phi a b) ∧ PLDomain e (sourceSlab phi a b) ∧
      frontier (sourceSlab phi a b) = (sourceSlab phi a b ∩ frontier R) ∪
        (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)) ∧
      IsCompact (sourceSlab phi b (a + p)) ∧ PLDomain e (sourceSlab phi b (a + p)) ∧
      frontier (sourceSlab phi b (a + p)) = (sourceSlab phi b (a + p) ∩ frontier R) ∪
        (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)) ∧
      sourceSlab phi a b ∪ sourceSlab phi b (a + p) = R ∧
      sourceSlab phi a b ∩ sourceSlab phi b (a + p) =
        sourceSurface phi (a : C) ∪ sourceSurface phi (b : C) ∧
      Disjoint (sourceSurface phi (a : C)) (sourceSurface phi (b : C)) ∧
      (∀ theta ∈ ({a, b} : Set ℝ), IsCompact (sourceSurface phi (theta : C)) ∧
        (sourceSurface phi (theta : C)).Nonempty) ∧
      ∀ uv ∈ ({(a, b), (b, a + p)} : Set (ℝ × ℝ)),
        ∀ theta ∈ ({uv.1, uv.2} : Set ℝ),
          ∀ x ∈ sourceSurface phi (theta : C) ∩ frontier R,
            ∃ (psi lambda : V3 →ᴬ[ℝ] ℝ) (w v : V3)
                (G : OpenPartialHomeomorph X V3),
              psi.contLinear w = 1 ∧ psi.contLinear v = 0 ∧
              lambda.contLinear v = 1 ∧ x ∈ G.source ∧ psi (G x) = 0 ∧
              (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
              (∀ y ∈ G.source, y ∈ sourceSlab phi uv.1 uv.2 ↔ 0 ≤ psi (G y)) ∧
              (∀ y ∈ G.source, y ∈ sourceSlab phi uv.1 uv.2 ∩ frontier R ↔
                psi (G y) = 0 ∧ 0 ≤ lambda (G y)) ∧
              ∀ y ∈ G.source, y ∈ sourceSurface phi (theta : C) ↔
                psi (G y) = 0 ∧ lambda (G y) ≤ 0 := by
  classical
  let : T2Space ((Fin 2 → ℝ) ⧸ (hamiltonLowerPeriodLattice (Fin 2)).toAddSubgroup) :=
    (hamiltonLowerLatticePiEquiv (Fin 2)).isEmbedding.t2Space
  let q : C(R, C) := (sourcePhase phi).comp
    ⟨latticeHandleDomainEquiv (Fin 1) (Fin 2) L,
      (latticeHandleDomainEquiv (Fin 1) (Fin 2) L).continuous⟩
  obtain ⟨a, ha, hAc, hAne, hA, hAB⟩ :=
    exists_sourcePhase_regular_level_between e d hd phi hphi F
      (p / 4) (p / 3) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨b, hb, hBc, hBne, hB, hBB⟩ :=
    exists_sourcePhase_regular_level_between e d hd phi hphi F
      (2 * p / 3) (3 * p / 4) (by norm_num) (by norm_num) (by norm_num)
  have ha0 : 0 < a := by linarith [ha.1]
  have hab : a < b := by linarith [ha.2, hb.1]
  have hbp : b < p := by linarith [hb.2]
  have hreg (theta : ℝ) (htheta : theta ∈ ({a, b} : Set ℝ)) (x : R)
      (hxt : q x = (theta : C)) :
      ∃ (d0 : ℝ) (ell : V3 →ᴬ[ℝ] ℝ) (v : V3) (T : OpenPartialHomeomorph X V3),
        (d0 : C) = (theta : C) ∧ ell.contLinear v = 1 ∧
        (x : X) ∈ T.source ∧ ell (T x) = 0 ∧
        (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
        ∀ y : R, (y : X) ∈ T.source → q y = ((ell (T y) + d0 : ℝ) : C) := by
    rcases htheta with rfl | rfl
    · obtain ⟨d0, ell, v, T, hd0, hv, hx, hz, hT, hq, _⟩ := hA x hxt
      exact ⟨d0, ell, v, T, hd0, hv, hx, hz, hT, hq⟩
    · obtain ⟨d0, ell, v, T, hd0, hv, hx, hz, hT, hq, _⟩ := hB x hxt
      exact ⟨d0, ell, v, T, hd0, hv, hx, hz, hT, hq⟩
  have hregB (theta : ℝ) (htheta : theta ∈ ({a, b} : Set ℝ)) (x : R)
      (hxB : (x : X) ∈ frontier R) (hxt : q x = (theta : C)) :
      ∃ (d0 : ℝ) (psi ell : V3 →ᴬ[ℝ] ℝ) (u v : V3) (T : OpenPartialHomeomorph X V3),
        (d0 : C) = (theta : C) ∧ psi.contLinear u = 1 ∧
        ell.contLinear v = 1 ∧ psi.contLinear v = 0 ∧
        (x : X) ∈ T.source ∧ ell (T x) = 0 ∧ psi (T x) = 0 ∧
        (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ T.source, y ∈ R ↔ 0 ≤ psi (T y)) ∧
        (∀ y ∈ T.source, y ∈ frontier R ↔ psi (T y) = 0) ∧
        ∀ y : R, (y : X) ∈ T.source → q y = ((ell (T y) + d0 : ℝ) : C) := by
    rcases htheta with rfl | rfl
    · obtain ⟨d0, psi, ell, u, v, T, hd0, hpu, hlv, hpv, hx, hl, hp,
          hT, hTR, hTB, hq, _⟩ := hAB x hxB hxt
      exact ⟨d0, psi, ell, u, v, T, hd0, hpu, hlv, hpv, hx, hl, hp, hT, hTR, hTB, hq⟩
    · obtain ⟨d0, psi, ell, u, v, T, hd0, hpu, hlv, hpv, hx, hl, hp,
          hT, hTR, hTB, hq, _⟩ := hBB x hxB hxt
      exact ⟨d0, psi, ell, u, v, T, hd0, hpu, hlv, hpv, hx, hl, hp, hT, hTR, hTB, hq⟩
  have hR := isCompact_latticeHandleDomain (Fin 1) (Fin 2) L
  obtain ⟨hPL, hfront⟩ := plDomain_relative_circle_slab e hphi.source_domain hR p q
    ha0 hab hbp hreg hregB
  have htheta (t : ℝ) (ht : t ∈ ({b, a + p} : Set ℝ)) :
      ∃ s ∈ ({a, b} : Set ℝ), (s : C) = (t : C) := by
    rcases ht with rfl | rfl
    · exact ⟨t, Or.inr rfl, rfl⟩
    · exact ⟨a, Or.inl rfl, (AddCircle.coe_add_period p a).symm⟩
  obtain ⟨hPL', hfront'⟩ := plDomain_relative_shifted_circle_slab e hphi.source_domain hR p q
    (by linarith : (a + b) / 2 < b) (by linarith : b < a + p)
    (by linarith : a + p < (a + b) / 2 + p)
    (fun theta ht x hx => by
      obtain ⟨s, hs, hst⟩ := htheta theta ht
      simpa only [hst] using hreg s hs x (hx.trans hst.symm))
    (fun theta ht x hxB hx => by
      obtain ⟨s, hs, hst⟩ := htheta theta ht
      simpa only [hst] using hregB s hs x hxB (hx.trans hst.symm))
  have hphases (u v : ℝ) : Subtype.val '' (q ⁻¹' {(u : C), (v : C)}) =
      sourceSurface phi (u : C) ∪ sourceSurface phi (v : C) := by
    rw [show ({(u : C), (v : C)} : Set C) = {(u : C)} ∪ {(v : C)} by
      ext; simp [or_comm], preimage_union, image_union]
    rfl
  have hcompact (u v : ℝ) : IsCompact (sourceSlab phi u v) := by
    let : CompactSpace R := isCompact_iff_compactSpace.mp hR
    exact ((AddCircle.isCompact_closedIntervalArc p u v).isClosed.preimage q.continuous).isCompact.image
      continuous_subtype_val
  have hpartition : sourceSlab phi a b ∪ sourceSlab phi b (a + p) = R ∧
      sourceSlab phi a b ∩ sourceSlab phi b (a + p) =
        sourceSurface phi (a : C) ∪ sourceSurface phi (b : C) := by
    have hc := AddCircle.compl_interior_closedIntervalArc p ha0 hab hbp
    have hf := AddCircle.frontier_closedIntervalArc p ha0 hab.le hbp
    have hclosed := (AddCircle.isCompact_closedIntervalArc p a b).isClosed
    constructor
    · apply Subset.antisymm
      · exact union_subset (sourceSlab_subset phi a b) (sourceSlab_subset phi b (a + p))
      · intro x hx
        let x' : R := ⟨x, hx⟩
        by_cases hq : q x' ∈ interior (AddCircle.closedIntervalArc p a b)
        · exact Or.inl ((mem_sourceSlab_iff phi a b x').mpr (interior_subset hq))
        · exact Or.inr ((mem_sourceSlab_iff phi b (a + p) x').mpr (hc ▸ hq))
    · ext x
      constructor
      · intro hx
        let x' : R := ⟨x, sourceSlab_subset phi a b hx.1⟩
        have hq := (mem_sourceSlab_iff phi a b x').mp hx.1
        have hqc := (mem_sourceSlab_iff phi b (a + p) x').mp hx.2
        have hqf : q x' ∈ frontier (AddCircle.closedIntervalArc p a b) := by
          rw [frontier, hclosed.closure_eq]
          exact ⟨hq, show q x' ∈ (interior (AddCircle.closedIntervalArc p a b))ᶜ from
            hc.symm ▸ hqc⟩
        rw [hf] at hqf
        rcases hqf with hqa | hqb
        · exact Or.inl ((mem_sourceSurface_iff phi (a : C) x').mpr hqa)
        · exact Or.inr ((mem_sourceSurface_iff phi (b : C) x').mpr hqb)
      · intro hx
        have hxR : x ∈ R := hx.elim (fun h => sourceSurface_subset phi (a : C) h)
          (fun h => sourceSurface_subset phi (b : C) h)
        let x' : R := ⟨x, hxR⟩
        have hqf : q x' ∈ frontier (AddCircle.closedIntervalArc p a b) := by
          rw [hf]
          rcases hx with hx | hx
          · exact Or.inl ((mem_sourceSurface_iff phi (a : C) x').mp hx)
          · exact Or.inr ((mem_sourceSurface_iff phi (b : C) x').mp hx)
        rw [frontier, hclosed.closure_eq] at hqf
        exact ⟨(mem_sourceSlab_iff phi a b x').mpr hqf.1,
          (mem_sourceSlab_iff phi b (a + p) x').mpr (hc ▸ hqf.2)⟩
  refine ⟨a, ha, b, hb, hcompact a b, hPL,
    hfront.trans (by rw [hphases]; rfl),
    hcompact b (a + p), hPL', ?_, hpartition.1, hpartition.2, ?_, ?_, ?_⟩
  · exact hfront'.trans (by rw [hphases, AddCircle.coe_add_period,
      union_comm (sourceSurface phi (b : C))]; rfl)
  · apply disjoint_left.mpr
    intro x hxA hxB
    let x' : R := ⟨x, sourceSurface_subset phi (a : C) hxA⟩
    have heq : (a : C) = (b : C) :=
      ((mem_sourceSurface_iff phi (a : C) x').mp hxA).symm.trans
        ((mem_sourceSurface_iff phi (b : C) x').mp hxB)
    have haI : a ∈ Ico (0 : ℝ) (0 + p) := by constructor <;> linarith
    have hbI : b ∈ Ico (0 : ℝ) (0 + p) := by constructor <;> linarith
    exact (ne_of_lt hab) ((AddCircle.coe_eq_coe_iff_of_mem_Ico haI hbI).mp heq)
  · intro theta ht
    rcases ht with rfl | rfl
    · exact ⟨hAc.image continuous_subtype_val, hAne.image _⟩
    · exact ⟨hBc.image continuous_subtype_val, hBne.image _⟩

  · intro uv huv theta ht x hx
    have hseam : ∃ c : ℝ, c < uv.1 ∧ uv.1 < uv.2 ∧ uv.2 < c + p := by
      rcases huv with huv | huv
      · rw [huv]
        exact ⟨0, ha0, hab, by simpa only [zero_add] using hbp⟩
      · rw [huv]
        exact ⟨(a + b) / 2, by dsimp; linarith,
          by dsimp; linarith, by dsimp; linarith⟩
    obtain ⟨c, hc, huvlt, hvc⟩ := hseam
    obtain ⟨s, hs, hst⟩ : ∃ s ∈ ({a, b} : Set ℝ), (s : C) = (theta : C) := by
      rcases huv with huv | huv
      · rw [huv] at ht
        exact ⟨theta, ht, rfl⟩
      · rw [huv] at ht
        exact htheta theta ht
    let x' : R := ⟨x, sourceSurface_subset phi (theta : C) hx.1⟩
    have hxt : q x' = (theta : C) := (mem_sourceSurface_iff phi (theta : C) x').mp hx.1
    obtain ⟨d0, psi, ell, u, v, T, hd0, hpu, hlv, hpv, hxT, hlx, hpx,
        hT, hTR, hTB, hq⟩ := hregB s hs x' hx.2 (hxt.trans hst.symm)
    obtain ⟨lambda, v', G, hpv', hlv', hxG, _, hpxG, hG, _, hGN, hGB, hGS⟩ :=
      exists_relative_shifted_circle_endpoint_chart_with_tangent e p q hc huvlt hvc ht
        (hd0.trans hst) psi ell u v T hpu hlv hpv hxT hpx hlx hT hTR hTB hq
    have hNmem (y : X) : y ∈ sourceSlab phi uv.1 uv.2 ↔
        ∃ hy : y ∈ R, q ⟨y, hy⟩ ∈ AddCircle.closedIntervalArc p uv.1 uv.2 := by
      constructor
      · rintro ⟨z, hz, rfl⟩; exact ⟨z.property, hz⟩
      · rintro ⟨hy, hq⟩; exact ⟨⟨y, hy⟩, hq, rfl⟩
    have hSmem (y : X) : y ∈ sourceSurface phi (theta : C) ↔
        ∃ hy : y ∈ R, q ⟨y, hy⟩ = (theta : C) := by
      constructor
      · rintro ⟨z, hz, rfl⟩; exact ⟨z.property, hz⟩
      · rintro ⟨hy, hq⟩; exact ⟨⟨y, hy⟩, hq, rfl⟩
    refine ⟨psi, lambda, u, v', G, hpu, hpv', hlv', hxG, hpxG, hG,
      fun y hy => (hNmem y).trans (hGN y hy), ?_,
      fun y hy => (hSmem y).trans (hGS y hy)⟩
    intro y hy
    change (y ∈ sourceSlab phi uv.1 uv.2 ∧ y ∈ frontier R) ↔ _
    rw [hNmem, and_comm]
    exact hGB y hy

theorem exists_complementary_sourceSlabs_with_marked_corners
    {α β : Type*} (e : α → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3)
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (F : (ContinuousMap.id H).HomotopyRel phi B) :
    ∃ a ∈ Ioo (p / 4) (p / 3), ∃ b ∈ Ioo (2 * p / 3) (3 * p / 4),
      IsCompact (sourceSlab phi a b) ∧ PLDomain e (sourceSlab phi a b) ∧
      frontier (sourceSlab phi a b) = (sourceSlab phi a b ∩ frontier R) ∪
        (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)) ∧
      IsCompact (sourceSlab phi b (a + p)) ∧ PLDomain e (sourceSlab phi b (a + p)) ∧
      frontier (sourceSlab phi b (a + p)) = (sourceSlab phi b (a + p) ∩ frontier R) ∪
        (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)) ∧
      sourceSlab phi a b ∪ sourceSlab phi b (a + p) = R ∧
      sourceSlab phi a b ∩ sourceSlab phi b (a + p) =
        sourceSurface phi (a : C) ∪ sourceSurface phi (b : C) ∧
      Disjoint (sourceSurface phi (a : C)) (sourceSurface phi (b : C)) ∧
      (∀ theta ∈ ({a, b} : Set ℝ), IsCompact (sourceSurface phi (theta : C)) ∧
        (sourceSurface phi (theta : C)).Nonempty) ∧
      ∀ uv ∈ ({(a, b), (b, a + p)} : Set (ℝ × ℝ)),
        ∀ theta ∈ ({uv.1, uv.2} : Set ℝ),
          ∀ x ∈ sourceSurface phi (theta : C) ∩ frontier R,
            ∃ (psi lambda : V3 →ᴬ[ℝ] ℝ) (w : V3) (G : OpenPartialHomeomorph X V3),
              psi.contLinear w = 1 ∧ x ∈ G.source ∧ psi (G x) = 0 ∧
              (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
              (∀ y ∈ G.source, y ∈ sourceSlab phi uv.1 uv.2 ↔ 0 ≤ psi (G y)) ∧
              (∀ y ∈ G.source, y ∈ sourceSlab phi uv.1 uv.2 ∩ frontier R ↔
                psi (G y) = 0 ∧ 0 ≤ lambda (G y)) ∧
              ∀ y ∈ G.source, y ∈ sourceSurface phi (theta : C) ↔
                psi (G y) = 0 ∧ lambda (G y) ≤ 0 := by
  obtain ⟨a, ha, b, hb, hNc, hN, hNF, hMc, hM, hMF, hU, hI, hD, hS, hcharts⟩ :=
    exists_complementary_sourceSlabs_with_transverse_corners e d hd phi hphi F
  refine ⟨a, ha, b, hb, hNc, hN, hNF, hMc, hM, hMF, hU, hI, hD, hS, ?_⟩
  intro uv huv theta ht x hx
  obtain ⟨psi, lambda, w, v, G, hw, _, _, hchart⟩ := hcharts uv huv theta ht x hx
  exact ⟨psi, lambda, w, G, hw, hchart⟩

theorem exists_complementary_sourceSlabs
    {α β : Type*} (e : α → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3)
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (F : (ContinuousMap.id H).HomotopyRel phi B) :
    ∃ a ∈ Ioo (p / 4) (p / 3), ∃ b ∈ Ioo (2 * p / 3) (3 * p / 4),
      IsCompact (sourceSlab phi a b) ∧ PLDomain e (sourceSlab phi a b) ∧
      frontier (sourceSlab phi a b) = (sourceSlab phi a b ∩ frontier R) ∪
        (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)) ∧
      IsCompact (sourceSlab phi b (a + p)) ∧ PLDomain e (sourceSlab phi b (a + p)) ∧
      frontier (sourceSlab phi b (a + p)) = (sourceSlab phi b (a + p) ∩ frontier R) ∪
        (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)) ∧
      sourceSlab phi a b ∪ sourceSlab phi b (a + p) = R ∧
      sourceSlab phi a b ∩ sourceSlab phi b (a + p) =
        sourceSurface phi (a : C) ∪ sourceSurface phi (b : C) ∧
      Disjoint (sourceSurface phi (a : C)) (sourceSurface phi (b : C)) ∧
      (∀ theta ∈ ({a, b} : Set ℝ), IsCompact (sourceSurface phi (theta : C)) ∧
        (sourceSurface phi (theta : C)).Nonempty) := by
  obtain ⟨a, ha, b, hb, hNc, hN, hNF, hMc, hM, hMF, hU, hI, hD, hS, _⟩ :=
    exists_complementary_sourceSlabs_with_marked_corners e d hd phi hphi F
  exact ⟨a, ha, b, hb, hNc, hN, hNF, hMc, hM, hMF, hU, hI, hD, hS⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
