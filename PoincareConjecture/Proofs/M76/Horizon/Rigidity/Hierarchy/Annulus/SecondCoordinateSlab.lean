import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.SecondCoordinateSurface
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.CircleSlabDomain









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p

private theorem exists_second_phase_between {Z : Set C0} (hZ : Z.Finite)
    {lo hi : ℝ} (hlo : 0 ≤ lo) (hhi : hi ≤ p) (hlt : lo < hi) :
    ∃ t ∈ Ioo lo hi, (t : C0) ∉ Z := by
  have hinj : InjOn (fun t : ℝ => (t : C0)) (Ioo lo hi) := by
    intro x hx y hy hxy
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := 0)
      (show x ∈ Ico 0 (0 + p) by constructor <;> linarith [hx.1, hx.2])
      (show y ∈ Ico 0 (0 + p) by constructor <;> linarith [hy.1, hy.2])).mp hxy
  obtain ⟨_, ⟨t, ht, rfl⟩, htZ⟩ := ((Ioo_infinite hlt).image hinj).exists_notMem_finite hZ
  exact ⟨t, ht, htZ⟩

theorem exists_hamiltonZero_second_coordinate_slab {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    {R : Set X0} (he : PLDomain e R) :
    ∃ a ∈ Ioo (p / 4) (p / 3), ∃ b ∈ Ioo (2 * p / 3) (3 * p / 4),
      let q := hamiltonZeroSecondCircleMap phi
      let N := R ∩ q ⁻¹' AddCircle.closedIntervalArc p a b
      IsCompact N ∧ PLDomain e N ∧
      frontier N = (N ∩ frontier R) ∪ (R ∩ q ⁻¹' {(a : C0), (b : C0)}) ∧
      Disjoint (R ∩ q ⁻¹' {(a : C0)}) (R ∩ q ⁻¹' {(b : C0)}) ∧
      ∀ theta ∈ ({a, b} : Set ℝ),
        HamiltonZeroSecondCoordinateRegularity e R phi (theta : C0) := by
  classical
  let : T2Space X0 :=
    (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).isEmbedding.t2Space
  let q : C(R, C0) := (hamiltonZeroSecondCircleMap phi).comp
    ⟨Subtype.val, continuous_subtype_val⟩
  obtain ⟨Z, hZ, hregular⟩ :=
    exists_hamiltonZero_second_coordinate_finite_regular_values e d hd phi hphi he
  obtain ⟨a, ha, haZ⟩ := exists_second_phase_between hZ
    (by norm_num : (0 : ℝ) ≤ p / 4) (by norm_num : p / 3 ≤ p) (by norm_num)
  obtain ⟨b, hb, hbZ⟩ := exists_second_phase_between hZ
    (by norm_num : (0 : ℝ) ≤ 2 * p / 3) (by norm_num : 3 * p / 4 ≤ p) (by norm_num)
  have ha0 : 0 < a := by linarith [ha.1]
  have hab : a < b := by linarith [ha.2, hb.1]
  have hbp : b < p := by linarith [hb.2]
  have hreg (theta : ℝ) (htheta : theta ∈ ({a, b} : Set ℝ)) :
      HamiltonZeroSecondCoordinateRegularity e R phi (theta : C0) := by
    rcases htheta with rfl | rfl
    · exact hregular _ haZ
    · exact hregular _ hbZ
  have hR : IsCompact R :=
    isCompact_hamiltonZeroAmbient.of_isClosed_subset he.closed (subset_univ _)
  obtain ⟨hPL, hfront⟩ := HamiltonIntervalTorus.plDomain_relative_circle_slab e he hR p q
    ha0 hab hbp (fun theta ht x hx => by
      obtain ⟨d0, ell, v, T, hd0, hv, hxT, hzero, hT, hformula, _⟩ := (hreg theta ht).1 x hx
      exact ⟨d0, ell, v, T, hd0, hv, hxT, hzero, hT, hformula⟩)
    (fun theta ht x hxB hx => by
      obtain ⟨d0, psi, ell, u, v, T, hd0, hpu, hlv, hpv, hxT, hlx, hpx,
        hT, hTR, hTB, hformula, _⟩ := (hreg theta ht).2 x hxB hx
      exact ⟨d0, psi, ell, u, v, T, hd0, hpu, hlv, hpv, hxT, hlx, hpx,
        hT, hTR, hTB, hformula⟩)
  have himage (S : Set C0) : Subtype.val '' (q ⁻¹' S) =
      R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · rintro ⟨hx, hq⟩
      exact ⟨⟨x, hx⟩, hq, rfl⟩
  rw [himage] at hPL
  rw [himage, himage] at hfront
  refine ⟨a, ha, b, hb, ?_, hPL, hfront, ?_, hreg⟩
  · exact hR.inter_right
      ((AddCircle.isCompact_closedIntervalArc p a b).isClosed.preimage
        (hamiltonZeroSecondCircleMap phi).continuous)
  · apply disjoint_left.mpr
    intro x hx hy
    have hcoe : (a : C0) = (b : C0) := hx.2.symm.trans hy.2
    have haI : a ∈ Ico (0 : ℝ) (0 + p) := by constructor <;> linarith
    have hbI : b ∈ Ico (0 : ℝ) (0 + p) := by constructor <;> linarith
    exact (ne_of_lt hab) ((AddCircle.coe_eq_coe_iff_of_mem_Ico haI hbI).mp hcoe)

end PoincareConjecture.M76
