import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.ThirdCoordinateSlab
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.ShiftedCircleSlabDomain









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p

theorem hamiltonZero_third_slab_of_regular_endpoints
    {ι : Type*} (e : ι → OpenPartialHomeomorph X0 V3) (phi : C(H0, H0))
    {R : Set X0} (he : PLDomain e R) {cut a b : ℝ}
    (ha : cut < a) (hab : a < b) (hb : b < cut + p)
    (hreg : ∀ theta ∈ ({a, b} : Set ℝ), HamiltonZeroThirdCoordinateRegularity e R phi (theta : C0)) :
    let q := hamiltonZeroThirdCircleMap phi
    let N := R ∩ q ⁻¹' AddCircle.closedIntervalArc p a b
    PLDomain e N ∧ frontier N = (N ∩ frontier R) ∪
      ((R ∩ q ⁻¹' {(a : C0)}) ∪ (R ∩ q ⁻¹' {(b : C0)})) := by
  let : T2Space X0 :=
    (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).isEmbedding.t2Space
  let : Fact (0 < p) := ⟨by norm_num⟩
  let q : C(R, C0) := (hamiltonZeroThirdCircleMap phi).comp
    ⟨Subtype.val, continuous_subtype_val⟩
  have hR : IsCompact R :=
    isCompact_hamiltonZeroAmbient.of_isClosed_subset he.closed (subset_univ _)
  obtain ⟨hPL, hfront⟩ := HamiltonIntervalTorus.plDomain_relative_shifted_circle_slab
    e he hR p q ha hab hb (fun theta ht x hx => by
      obtain ⟨d, ell, v, T, hd, hv, hxT, hz, hT, hq, _⟩ := (hreg theta ht).1 x hx
      exact ⟨d, ell, v, T, hd, hv, hxT, hz, hT, hq⟩)
    (fun theta ht x hxB hx => by
      obtain ⟨d, psi, ell, u, v, T, hd, hu, hv, huv, hxT, hlx, hpx, hT, hR, hB, hq, _⟩ :=
        (hreg theta ht).2 x hxB hx
      exact ⟨d, psi, ell, u, v, T, hd, hu, hv, huv, hxT, hlx, hpx, hT, hR, hB, hq⟩)
  have himage (S : Set C0) : Subtype.val '' (q ⁻¹' S) =
      R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' S := by
    ext x
    exact ⟨fun ⟨y, hy, heq⟩ => heq ▸ ⟨y.property, hy⟩,
      fun h => ⟨⟨x, h.1⟩, h.2, rfl⟩⟩
  rw [himage] at hPL
  rw [himage, himage] at hfront
  refine ⟨hPL, hfront.trans ?_⟩
  congr 1
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_insert_iff, mem_singleton_iff, mem_union]
  tauto

theorem exists_hamiltonZero_complementary_third_slabs
    {ι κ : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    {R : Set X0} (he : PLDomain e R) :
    ∃ a ∈ Ioo (p / 4) (p / 3), ∃ b ∈ Ioo (2 * p / 3) (3 * p / 4),
      (∀ theta ∈ ({a, b} : Set ℝ), HamiltonZeroThirdCoordinateRegularity e R phi (theta : C0)) ∧
      ∀ uv ∈ ({(a, b), (b, a + p)} : Set (ℝ × ℝ)),
        let q := hamiltonZeroThirdCircleMap phi
        let N := R ∩ q ⁻¹' AddCircle.closedIntervalArc p uv.1 uv.2
        PLDomain e N ∧ frontier N = (N ∩ frontier R) ∪
          ((R ∩ q ⁻¹' {(a : C0)}) ∪ (R ∩ q ⁻¹' {(b : C0)})) := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  obtain ⟨a, ha, b, hb, _, _, _, _, hreg⟩ :=
    exists_hamiltonZero_third_coordinate_slab e d hd phi hphi he
  have ha0 : 0 < a := by linarith [ha.1]
  have hab : a < b := by linarith [ha.2, hb.1]
  have hbp : b < p := by linarith [hb.2]
  refine ⟨a, ha, b, hb, hreg, ?_⟩
  intro uv huv
  rcases huv with huv | huv
  · rw [show uv = (a, b) from huv]
    exact hamiltonZero_third_slab_of_regular_endpoints e phi he ha0 hab (by simpa using hbp) hreg
  · rw [show uv = (b, a + p) from huv]
    have hreg' (theta : ℝ) (ht : theta ∈ ({b, a + p} : Set ℝ)) :
        HamiltonZeroThirdCoordinateRegularity e R phi (theta : C0) := by
      rcases ht with ht | ht
      · rw [show theta = b from ht]
        exact hreg b (Or.inr rfl)
      · rw [show theta = a + p from ht, AddCircle.coe_add_period]
        exact hreg a (Or.inl rfl)
    have h := hamiltonZero_third_slab_of_regular_endpoints e phi he
      (show (a + b) / 2 < b by linarith) (show b < a + p by linarith)
      (show a + p < (a + b) / 2 + p by linarith) hreg'
    simpa only [AddCircle.coe_add_period, union_comm] using h

end PoincareConjecture.M76
