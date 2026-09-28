import PoincareConjecture.Proofs.M76.Rigidity.SourceMeridianCutSphere
import PoincareConjecture.Proofs.M76.Rigidity.OriginalInwardSphere
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonPLIrreducibility










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "J" => Icc (0 : ℝ) 1
local notation "L0" => hamiltonLowerPeriodLattice (Fin 1)
local notation "T" => (Fin 1 → ℝ) ⧸ Submodule.toAddSubgroup (hamiltonLowerPeriodLattice (Fin 1))
local notation "X" => LatticeHandleAmbient (Fin 2) (Fin 1) L0
local notation "R" => latticeHandleDomain (Fin 2) (Fin 1) L0
local notation "H" => LatticeHandle (Fin 2) (Fin 1) L0
local notation "B" => latticeHandleBoundary (Fin 2) (Fin 1) L0

private instance : Fact (0 < 4 * (128 : ℝ)) := ⟨by norm_num⟩

open Classical in




theorem exists_source_meridian_inward_sphere
    {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3}
    (hI : IsPLIrreducible e R) (hd : StandardLatticeHandleAtlas (Fin 2) (Fin 1) L0 d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 2) (Fin 1) L0 phi))
    (F : (ContinuousMap.id H).HomotopyRel phi B)
    (j : V2 → X) (hj : PolyhedralPLInCharts e j D)
    (hemb : Topology.IsEmbedding (fun z : D => j z)) (hDR : MapsTo j D R)
    (hproper : ∀ z : D, j z ∈ frontier R ↔ (z : V2) ∈ Q)
    (hrim : ∀ z ∈ Q, j z = hamiltonStandardMeridianMap L0 z)
    {U : Set X} (hU : IsOpen U) (hDU : j '' D ⊆ U) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 / 2 ∧ ∃ P : OriginalDiskProduct e R j,
      MapsTo P.map (D ×ˢ I) U ∧
      (∀ z ∈ Q, ∀ t ∈ I, P.map (z, t) = hamiltonMeridianCutAmbientMap (z, a * t)) ∧
      (∀ v : ℝ, 0 < v → v ≤ 1 →
        IsOpen ((Subtype.val : R → X) ⁻¹' (P.map '' (D ×ˢ Ioo (-v) v))) ∧
        IsOpen ((Subtype.val : frontier R → X) ⁻¹' (P.map '' (Q ×ˢ Ioo (-v) v)))) ∧
      PLDomain e P.cutCarrier ∧ IsCompact P.cutCarrier ∧
      Nonempty (ChartwisePLSphere e (frontier P.cutCarrier)) ∧
      interior P.cutCarrier = interior R \ P.closedStrip ∧
      frontier P.cutCarrier = (frontier R \ P.openStrip) ∪ P.endDisks ∧
      P.closedStrip ∩ P.cutCarrier = P.endDisks ∧
      P.closedStrip ∪ P.cutCarrier = R ∧
      (interior P.cutCarrier).Nonempty ∧
      ∃ (s : Finset P.cutCarrier) (L : SimplicialComplex ℝ (s → ℝ × V3))
        (HB : L.space ≃ₜ frontier P.cutCarrier) (c : (s → ℝ × V3) × ℝ → X),
        L.faces.Finite ∧ PolyhedralPLInCharts e c (L.space ×ˢ J) ∧
        Topology.IsEmbedding (fun z : (L.space ×ˢ J : Set ((s → ℝ × V3) × ℝ)) => c z) ∧
        MapsTo c (L.space ×ˢ J) P.cutCarrier ∧
        (∀ x : L.space, c ((x : s → ℝ × V3), 0) = HB x) ∧
        (∀ z : (L.space ×ˢ J : Set ((s → ℝ × V3) × ℝ)),
          c z ∈ frontier P.cutCarrier ↔ (z : (s → ℝ × V3) × ℝ).2 = 0) ∧
        ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
          (∀ ε : ℝ, 0 < ε → ε ≤ δ →
            IsOpen ((Subtype.val : P.cutCarrier → X) ⁻¹' (c '' (L.space ×ˢ Ico 0 ε)))) ∧
          Nonempty (ChartwisePLSphere e (c '' (L.space ×ˢ {δ / 2}))) ∧
          c '' (L.space ×ˢ {δ / 2}) ⊆ interior P.cutCarrier ∧
          ∃ Db : Set X, Db ⊆ R ∧
            Nonempty (ChartwisePLBall e Db (c '' (L.space ×ˢ {δ / 2}))) := by
  classical
  let : T2Space T := hamiltonSolidTorusCircleEquiv.isEmbedding.t2Space
  obtain ⟨a, ha, hasmall, P, hPU, hmark, hopen, heK, hK, ⟨sph⟩,
    hint, hfront, hoverlap, hcover, hne⟩ :=
    exists_source_meridian_cut_sphere hI.1 hd phi hphi F j hj hemb hDR hproper hrim hU hDU
  obtain ⟨s, L, HB, c, hL, hc, hi, hinside, hbase, hproperC,
    δ, hδ, hδsmall, _, hopenC, hlevel, hlevelInt, _⟩ :=
    exists_original_inward_sphere hK heK hne sph isOpen_univ (subset_univ _)
  have hKR : P.cutCarrier ⊆ R := sdiff_subset
  obtain ⟨Db, hDbR, hDb⟩ := hI.2 _ (hlevelInt.trans (interior_mono hKR)) hlevel
  exact ⟨a, ha, hasmall, P, hPU, hmark, hopen, heK, hK, ⟨sph⟩,
    hint, hfront, hoverlap, hcover, hne, s, L, HB, c, hL, hc, hi, hinside,
    hbase, hproperC, δ, hδ, hδsmall, hopenC, hlevel, hlevelInt, Db, hDbR, hDb⟩

end PoincareConjecture.M76
