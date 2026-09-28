import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.CircleSlabDomain
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


def sourceSlab (phi : C(H, H)) (a b : ℝ) : Set X :=
  Subtype.val '' {x : R | sourcePhase phi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L x) ∈
    AddCircle.closedIntervalArc p a b}

theorem sourceSlab_subset (phi : C(H, H)) (a b : ℝ) : sourceSlab phi a b ⊆ R := by
  rintro _ ⟨x, _, rfl⟩
  exact x.property

theorem mem_sourceSlab_iff (phi : C(H, H)) (a b : ℝ) (x : R) :
    (x : X) ∈ sourceSlab phi a b ↔
      sourcePhase phi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L x) ∈
        AddCircle.closedIntervalArc p a b := by
  constructor
  · rintro ⟨y, hy, heq⟩
    exact (Subtype.ext heq : y = x) ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩



theorem exists_sourceSlab_with_marked_corners
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
      Disjoint (sourceSurface phi (a : C)) (sourceSurface phi (b : C)) ∧
      (∀ theta ∈ ({a, b} : Set ℝ), IsCompact (sourceSurface phi (theta : C)) ∧
        (sourceSurface phi (theta : C)).Nonempty) ∧
      ∀ theta ∈ ({a, b} : Set ℝ),
        ∀ x ∈ sourceSurface phi (theta : C) ∩ frontier R,
          ∃ (psi lambda : V3 →ᴬ[ℝ] ℝ) (u : V3) (G : OpenPartialHomeomorph X V3),
            psi.contLinear u = 1 ∧ x ∈ G.source ∧ psi (G x) = 0 ∧
            (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
            (∀ y ∈ G.source, y ∈ sourceSlab phi a b ↔ 0 ≤ psi (G y)) ∧
            (∀ y ∈ G.source, y ∈ sourceSlab phi a b ∩ frontier R ↔
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
  have hphases : Subtype.val '' (q ⁻¹' {(a : C), (b : C)}) =
      sourceSurface phi (a : C) ∪ sourceSurface phi (b : C) := by
    rw [show ({(a : C), (b : C)} : Set C) = {(a : C)} ∪ {(b : C)} by
      ext; simp [or_comm], preimage_union, image_union]
    rfl
  have hN : IsCompact (sourceSlab phi a b) := by
    let : CompactSpace R := isCompact_iff_compactSpace.mp hR
    exact ((AddCircle.isCompact_closedIntervalArc p a b).isClosed.preimage q.continuous).isCompact.image
      continuous_subtype_val
  refine ⟨a, ha, b, hb, hN, hPL, hfront.trans (by rw [hphases]; rfl), ?_, ?_, ?_⟩
  · apply disjoint_left.mpr
    intro x hxA hxB
    let x' : R := ⟨x, sourceSurface_subset phi (a : C) hxA⟩
    have hqa := (mem_sourceSurface_iff phi (a : C) x').mp hxA
    have hqb := (mem_sourceSurface_iff phi (b : C) x').mp hxB
    have heq : (a : C) = (b : C) := hqa.symm.trans hqb
    have haI : a ∈ Ico (0 : ℝ) (0 + p) := by constructor <;> linarith
    have hbI : b ∈ Ico (0 : ℝ) (0 + p) := by constructor <;> linarith
    exact (ne_of_lt hab) ((AddCircle.coe_eq_coe_iff_of_mem_Ico haI hbI).mp heq)
  · intro theta htheta
    rcases htheta with rfl | rfl
    · exact ⟨hAc.image continuous_subtype_val, hAne.image _⟩
    · exact ⟨hBc.image continuous_subtype_val, hBne.image _⟩
  · intro theta htheta x hx
    let x' : R := ⟨x, sourceSurface_subset phi (theta : C) hx.1⟩
    have hxt : q x' = (theta : C) := (mem_sourceSurface_iff phi (theta : C) x').mp hx.1
    obtain ⟨d0, psi, ell, u, v, T, hd0, hpu, hlv, hpv, hxT, hlx, hpx,
        hT, hTR, hTB, hq⟩ := hregB theta htheta x' hx.2 hxt
    obtain ⟨lambda, G, hxG, _, hpxG, hG, _, hGN, hGB, hGS⟩ :=
      exists_relative_circle_endpoint_chart e p q ha0 hab hbp htheta hd0
        psi ell u v T hpu hlv hpv hxT hpx hlx hT hTR hTB hq
    have hNmem (y : X) : y ∈ sourceSlab phi a b ↔
        ∃ hy : y ∈ R, q ⟨y, hy⟩ ∈ AddCircle.closedIntervalArc p a b := by
      constructor
      · rintro ⟨z, hz, rfl⟩; exact ⟨z.property, hz⟩
      · rintro ⟨hy, hq⟩; exact ⟨⟨y, hy⟩, hq, rfl⟩
    have hSmem (y : X) : y ∈ sourceSurface phi (theta : C) ↔
        ∃ hy : y ∈ R, q ⟨y, hy⟩ = (theta : C) := by
      constructor
      · rintro ⟨z, hz, rfl⟩; exact ⟨z.property, hz⟩
      · rintro ⟨hy, hq⟩; exact ⟨⟨y, hy⟩, hq, rfl⟩
    refine ⟨psi, lambda, u, G, hpu, hxG, hpxG, hG,
      fun y hy => (hNmem y).trans (hGN y hy), ?_,
      fun y hy => (hSmem y).trans (hGS y hy)⟩
    intro y hy
    change (y ∈ sourceSlab phi a b ∧ y ∈ frontier R) ↔ _
    rw [hNmem, and_comm]
    exact hGB y hy

end PoincareConjecture.M76.HamiltonIntervalTorus
