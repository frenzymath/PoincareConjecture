import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.InstalledGeometry
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Compression.MarkedCorners
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.MarkedCoverSideInjection

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p

theorem hamiltonZero_installed_second_slabs_pi1_injective
    {ι : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (phi psi chi : C(H0, H0)) {R A : Set X0}
    (heR : PLDomain e R) (hA : IsCompact A) (hAR : A ⊆ interior R)
    (hfixed : ∀ x ∉ A, hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    (hreg : ∀ theta ∈ ({a, b} : Set ℝ),
      HamiltonZeroSecondCoordinateRegularity e R phi (theta : C0))
    (geometry : HamiltonZeroSecondPhaseGeometry e R psi a b)
    (hsecond : hamiltonZeroSecondCircleMap chi = hamiltonZeroSecondCircleMap psi)
    (hboundary : (frontier R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(a : C0)}).Nonempty) :
    ∀ side : Bool,
      let N := R ∩ hamiltonZeroSecondCircleMap chi ⁻¹'
        AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
      ∀ x : N, Function.Injective
        (FundamentalGroup.map (ContinuousMap.inclusion (inter_subset_left : N ⊆ R)) x) := by
  classical
  let : Fact (0 < p) := ⟨by norm_num⟩
  let : TopologicalSpace.MetrizableSpace X0 :=
    (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).isEmbedding.metrizableSpace
  let : MetricSpace X0 := TopologicalSpace.metrizableSpaceMetric X0
  let q := hamiltonZeroSecondCircleMap psi
  let face (theta : ℝ) := R ∩ q ⁻¹' {(theta : C0)}
  let lo (side : Bool) : ℝ := if side then b else a
  let up (side : Bool) : ℝ := if side then a + p else b
  let cut (side : Bool) : ℝ := if side then (a + b) / 2 else 0
  let slab (side : Bool) := R ∩ q ⁻¹' AddCircle.closedIntervalArc p (lo side) (up side)
  have hfaceNe : (face a).Nonempty := by
    obtain ⟨x, hxB, hxq⟩ := hboundary
    have hxA : x ∉ A := fun h => hxB.2 (hAR h)
    have hqfixed : q x = hamiltonZeroSecondCircleMap phi x := by
      rw [hamiltonZeroSecondCircleMap_ambient, hamiltonZeroSecondCircleMap_ambient, hfixed x hxA]
    exact ⟨x, heR.closed.frontier_subset hxB, hqfixed.trans hxq⟩
  have hinj (side : Bool) (theta : ℝ) (ht : theta ∈ ({a, b} : Set ℝ)) :
      ∃ hSN : face theta ⊆ slab side, ∀ x : face theta,
        Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hSN) x) :=
    (geometry.slabs side).2.2 theta ht
  have hcorners (side : Bool) (theta : ℝ) (ht : theta ∈ ({a, b} : Set ℝ))
      (x : X0) (hx : x ∈ face theta ∩ frontier R) :
      ∃ (normal tangent : V3 →ᴬ[ℝ] ℝ) (w v : V3) (G : OpenPartialHomeomorph X0 V3),
        normal.contLinear w = 1 ∧ normal.contLinear v = 0 ∧ tangent.contLinear v = 1 ∧
        x ∈ G.source ∧ (∀ y ∈ G.source, y ∈ slab side ↔ 0 ≤ normal (G y)) ∧
        ∀ y ∈ G.source, y ∈ face theta ↔ normal (G y) = 0 ∧ tangent (G y) ≤ 0 := by
    obtain ⟨theta', ht', heq⟩ : ∃ theta' ∈ ({lo side, up side} : Set ℝ),
        (theta' : C0) = (theta : C0) := by
      cases side with
      | false => exact ⟨theta, ht, rfl⟩
      | true =>
        rcases ht with ht | ht
        · exact ⟨a + p, Or.inr rfl, by rw [AddCircle.coe_add_period, show theta = a from ht]⟩
        · exact ⟨b, Or.inl rfl, by rw [show theta = b from ht]⟩
    have hl : cut side < lo side := by cases side <;> dsimp [cut, lo] <;> linarith
    have hlu : lo side < up side := by cases side <;> dsimp [lo, up] <;> linarith
    have hu : up side < cut side + p := by cases side <;> dsimp [cut, up] <;> linarith
    have hreg' : HamiltonZeroSecondCoordinateRegularity e R phi (theta' : C0) := heq.symm ▸ hreg theta ht
    have hx' : x ∈ (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(theta' : C0)}) ∩ frontier R :=
      heq.symm ▸ hx
    obtain ⟨normal, tangent, w, v, G, hw, hv, htv, hxG, _, _, hN, _, hS⟩ :=
      exists_hamiltonZero_second_slab_marked_corner_of_supported_map e phi psi hA.isClosed hAR
        hfixed hl hlu hu ht' hreg' hx'
    refine ⟨normal, tangent, w, v, G, hw, hv, htv, hxG, hN, ?_⟩
    simpa only [heq] using hS
  have hclosed (theta : ℝ) : IsClosed (face theta) :=
    heR.closed.inter (isClosed_singleton.preimage q.continuous)
  have hdis : Disjoint (face a) (face b) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact hab.ne ((AddCircle.coe_eq_coe_iff_of_mem_Ico
      (show a ∈ Ico (0 : ℝ) (0 + p) by constructor <;> linarith)
      (show b ∈ Ico (0 : ℝ) (0 + p) by constructor <;> linarith)).mp (hx.2.symm.trans hy.2))
  have harc := HamiltonIntervalTorus.compl_interior_shifted_phase_arc p ha hab (by simpa using hb)
  have harcclosed := (AddCircle.isCompact_closedIntervalArc p a b).isClosed
  have hmeetArc : AddCircle.closedIntervalArc p a b ∩ AddCircle.closedIntervalArc p b (a + p) =
      {(a : C0), (b : C0)} := by
    calc
      _ = frontier (AddCircle.closedIntervalArc p a b) := by
        rw [frontier, harcclosed.closure_eq]
        change _ = AddCircle.closedIntervalArc p a b ∩ (interior (AddCircle.closedIntervalArc p a b))ᶜ
        rw [harc]
      _ = _ := AddCircle.frontier_closedIntervalArc p ha hab.le hb
  have hcover : slab false ∪ slab true = R := by
    apply Subset.antisymm (union_subset inter_subset_left inter_subset_left)
    intro x hx
    by_cases h : q x ∈ interior (AddCircle.closedIntervalArc p a b)
    · exact Or.inl ⟨hx, show q x ∈ AddCircle.closedIntervalArc p a b from interior_subset h⟩
    · exact Or.inr ⟨hx, show q x ∈ AddCircle.closedIntervalArc p b (a + p) from harc ▸ h⟩
  have hmeet : slab false ∩ slab true = face a ∪ face b := by
    ext x
    change (x ∈ R ∧ q x ∈ AddCircle.closedIntervalArc p a b) ∧
      (x ∈ R ∧ q x ∈ AddCircle.closedIntervalArc p b (a + p)) ↔ _
    rw [and_and_and_comm, and_self, ← mem_inter_iff, hmeetArc]
    simp only [mem_insert_iff, mem_singleton_iff, mem_union, face, mem_inter_iff, mem_preimage]
    tauto
  have hinjR := marked_cover_sides_pi1_injective e
    (inter_subset_left : slab false ⊆ R) (inter_subset_left : slab true ⊆ R) hcover hmeet
    (hfaceNe.mono subset_union_left) isClosed_frontier (hclosed a) (hclosed b) hdis (by
      intro T hT
      obtain ⟨side, rfl⟩ : ∃ side : Bool, T = slab side := by
        rcases hT with h | h
        · exact ⟨false, h⟩
        · exact ⟨true, h⟩
      obtain ⟨heN, hfN, _⟩ := geometry.slabs side
      refine ⟨isCompact_hamiltonZeroAmbient.of_isClosed_subset heN.closed (subset_univ _),
        heN, hfN, ?_⟩
      intro P hP
      obtain ⟨theta, ht, rfl⟩ : ∃ theta ∈ ({a, b} : Set ℝ), P = face theta := by
        rcases hP with h | h
        · exact ⟨a, Or.inl rfl, h⟩
        · exact ⟨b, Or.inr rfl, h⟩
      exact ⟨hinj side theta ht, hcorners side theta ht⟩)
  intro side
  dsimp only
  rw [hsecond]
  cases side with
  | false => exact hinjR.1
  | true => exact hinjR.2

end PoincareConjecture.M76
