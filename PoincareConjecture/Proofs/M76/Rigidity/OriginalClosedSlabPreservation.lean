import PoincareConjecture.Proofs.M76.Rigidity.OriginalClosedSlabHandleHomotopies
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.HomotopyClosedSides

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem hamiltonZero_slab_side_preimages (phi : C(H0, H0))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 4 * 16)
    (hfront : frontier ((hamiltonZeroCircleMap phi) ⁻¹'
        AddCircle.closedIntervalArc (4 * 16) a b) =
      (hamiltonZeroCircleMap phi) ⁻¹' {(a : C0), (b : C0)})
    (G : C(unitInterval × X0, X0))
    (hzero : ∀ y, G (0, y) = hamiltonZeroAmbientMap phi y)
    (hlevels : ∀ t : unitInterval,
      (fun y => (Q0 (G (t, y))).2) ⁻¹' {(a : C0)} =
        (hamiltonZeroCircleMap phi) ⁻¹' {(a : C0)} ∧
      (fun y => (Q0 (G (t, y))).2) ⁻¹' {(b : C0)} =
        (hamiltonZeroCircleMap phi) ⁻¹' {(b : C0)}) :
    let A := AddCircle.closedIntervalArc (4 * 16) a b
    let R := (hamiltonZeroCircleMap phi) ⁻¹' A
    ∀ t : unitInterval,
      (fun y => (Q0 (G (t, y))).2) ⁻¹' A = R ∧
      (fun y => (Q0 (G (t, y))).2) ⁻¹' interior A = interior R ∧
      (fun y => (Q0 (G (t, y))).2) ⁻¹' (interior A)ᶜ = (interior R)ᶜ := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  let q := hamiltonZeroCircleMap phi
  let A := AddCircle.closedIntervalArc (4 * 16) a b
  let R := q ⁻¹' A
  let P : C(unitInterval × X0, C0) :=
    ⟨fun z => (Q0 (G z)).2, ((Q0).continuous.comp G.continuous).snd⟩
  change ∀ t : unitInterval,
    (fun y => P (t, y)) ⁻¹' A = R ∧
    (fun y => P (t, y)) ⁻¹' interior A = interior R ∧
    (fun y => P (t, y)) ⁻¹' (interior A)ᶜ = (interior R)ᶜ
  have hstart : (fun y => P (0, y)) = q := by
    funext y
    change (Q0 (G (0, y))).2 = q y
    rw [hzero]
    exact hamiltonZeroAmbientMap_circle phi y
  have hpair (t : unitInterval) :
      (fun y => P (t, y)) ⁻¹' {(a : C0), (b : C0)} =
        q ⁻¹' {(a : C0), (b : C0)} := by
    simp only [Set.insert_eq, preimage_union]
    exact congrArg₂ (fun U V : Set X0 => U ∪ V) (hlevels t).1 (hlevels t).2
  have hboundary : frontier A = {(a : C0), (b : C0)} :=
    AddCircle.frontier_closedIntervalArc (4 * 16) ha hab.le hb
  have hfrontP (t : unitInterval) :
      (fun y => P (t, y)) ⁻¹' frontier A =
        (fun y => P (0, y)) ⁻¹' frontier A := by
    rw [hboundary]
    exact (hpair t).trans (hpair 0).symm
  intro t
  have hclosed : (fun y => P (t, y)) ⁻¹' A = R := by
    have h := P.preimage_eq_of_frontier_preimage_eq
      (AddCircle.isCompact_closedIntervalArc (4 * 16) a b).isClosed hfrontP t
    rw [hstart] at h
    exact h
  have hinterior : (fun y => P (t, y)) ⁻¹' interior A = interior R := by
    calc
      (fun y => P (t, y)) ⁻¹' interior A =
          (fun y => P (t, y)) ⁻¹' A \ (fun y => P (t, y)) ⁻¹' frontier A := by
        rw [← self_sdiff_frontier A, preimage_sdiff]
      _ = R \ frontier R := by rw [hclosed, hboundary, hpair t, hfront]
      _ = interior R := self_sdiff_frontier R
  exact ⟨hclosed, hinterior, by rw [preimage_compl, hinterior]⟩

open Classical in

theorem exists_hamiltonZero_slab_preserving_adjustment {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0) :
    ∃ a ∈ Ioo ((4 * 16 : ℝ) / 4) ((4 * 16 : ℝ) / 3),
      ∃ b ∈ Ioo (2 * (4 * 16 : ℝ) / 3) (3 * (4 * 16 : ℝ) / 4),
        0 < a ∧ a < b ∧ b < 4 * 16 ∧
        let q := hamiltonZeroCircleMap phi
        let A := AddCircle.closedIntervalArc (4 * 16) a b
        let R := q ⁻¹' A
        let S := q ⁻¹' {(a : C0), (b : C0)}
        IsCompact R ∧ PLDomain e R ∧ frontier R = S ∧
        IsCompact (interior R)ᶜ ∧ PLDomain e (interior R)ᶜ ∧
        frontier (interior R)ᶜ = S ∧
        (interior R).Nonempty ∧ (interior (interior R)ᶜ).Nonempty ∧
        ∀ U0 : Set X0, IsOpen U0 → S ⊆ U0 →
          ∃ (G : C(unitInterval × X0, X0)) (gH : C(H0, H0))
            (H : phi.HomotopyRel gH B0)
            (Fend : (ContinuousMap.id H0).HomotopyRel gH B0),
            (∀ y, G (0, y) = hamiltonZeroAmbientMap phi y) ∧
            (∀ t y, y ∈ S → G (t, y) = hamiltonZeroAmbientMap phi y) ∧
            (∀ t y, y ∉ U0 → G (t, y) = hamiltonZeroAmbientMap phi y) ∧
            (∀ t : unitInterval,
              (fun y => (Q0 (G (t, y))).2) ⁻¹' {(a : C0)} = q ⁻¹' {(a : C0)} ∧
              (fun y => (Q0 (G (t, y))).2) ⁻¹' {(b : C0)} = q ⁻¹' {(b : C0)}) ∧
            (∀ t : unitInterval,
              (fun y => (Q0 (G (t, y))).2) ⁻¹' A = R ∧
              (fun y => (Q0 (G (t, y))).2) ⁻¹' interior A = interior R ∧
              (fun y => (Q0 (G (t, y))).2) ⁻¹' (interior A)ᶜ = (interior R)ᶜ) ∧
            hamiltonZeroAmbientMap gH =
              ⟨fun y => G (1, y),
                G.continuous.comp (continuous_const.prodMk continuous_id)⟩ ∧
            ChartwisePLMap e d
              (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 gH) ∧
            Fend = F.trans H ∧
            (∀ t x, H (t, x) = hamiltonZeroAmbientEquiv
              (G (t, hamiltonZeroAmbientEquiv.symm x))) ∧
            (∀ t x, x ∈ hamiltonZeroAmbientEquiv '' S → H (t, x) = phi x) ∧
            (∀ t x, x ∉ hamiltonZeroAmbientEquiv '' U0 → H (t, x) = phi x) := by
  obtain ⟨a, haI, b, hbI, ha, hab, hb, _, _, _, _, _,
    hR, he, hfront, hminus, heminus, hfrontminus, hne, hneminus, _,
    eta, _, _, _, _, hfamily⟩ :=
    exists_hamiltonZero_adjusted_handle_homotopies e d hd phi hphi F
  refine ⟨a, haI, b, hbI, ha, hab, hb, hR, he, hfront,
    hminus, heminus, hfrontminus, hne, hneminus, ?_⟩
  intro U0 hU0 hSU0
  obtain ⟨s, L, HB, c, _, _, _, _, _, delta, _, _, _, _, _,
    v, _, _, _, _, _, r, _, _, _, D, w, G,
    _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _,
    _, hGzero, hGS, hGout, _, _, hlevels, _, _, hhandle, _⟩ :=
    hfamily U0 hU0 hSU0
  obtain ⟨gH, H, Fend, _, hroundtrip, hgPL, hconcat, hH, hHS, hHU, _⟩ := hhandle
  exact ⟨G, gH, H, Fend, hGzero, hGS, hGout, hlevels,
    hamiltonZero_slab_side_preimages phi ha hab hb hfront G hGzero hlevels,
    hroundtrip, hgPL, hconcat, hH, hHS, hHU⟩

end PoincareConjecture.M76
