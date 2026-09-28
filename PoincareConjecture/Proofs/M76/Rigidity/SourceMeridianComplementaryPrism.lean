import PoincareConjecture.Proofs.M76.Rigidity.SourceMeridianCutBall
import PoincareConjecture.Proofs.M76.Rigidity.MeridianCutPrismExtension
import PoincareConjecture.Proofs.M76.Rigidity.SourceComplementCylinder










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "T" => (Fin 1 → ℝ) ⧸ Submodule.toAddSubgroup (hamiltonLowerPeriodLattice (Fin 1))
local notation "X" => LatticeHandleAmbient (Fin 2) (Fin 1) L
local notation "R" => latticeHandleDomain (Fin 2) (Fin 1) L
local notation "H0" => LatticeHandle (Fin 2) (Fin 1) L
local notation "B0" => latticeHandleBoundary (Fin 2) (Fin 1) L
local notation "p" => (4 * (128 : ℝ))

private instance : Fact (0 < 4 * (128 : ℝ)) := ⟨by norm_num⟩




theorem exists_source_meridian_complementary_prism
    {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3}
    (hI : IsPLIrreducible e R) (hd : StandardLatticeHandleAtlas (Fin 2) (Fin 1) L d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 2) (Fin 1) L phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    (j : V2 → X) (hj : PolyhedralPLInCharts e j D)
    (hemb : Topology.IsEmbedding (fun z : D => j z)) (hDR : MapsTo j D R)
    (hproper : ∀ z : D, j z ∈ frontier R ↔ (z : V2) ∈ Q)
    (hrim : ∀ z ∈ Q, j z = hamiltonStandardMeridianMap L z)
    {U : Set X} (hU : IsOpen U) (hDU : j '' D ⊆ U) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 / 2 ∧ ∃ P : OriginalDiskProduct e R j,
      MapsTo P.map (D ×ˢ I) U ∧
      (∀ z ∈ Q, ∀ t ∈ I, P.map (z, t) = hamiltonMeridianCutAmbientMap (z, a * t)) ∧
      (∀ v : ℝ, 0 < v → v ≤ 1 →
        IsOpen ((Subtype.val : R → X) ⁻¹' (P.map '' (D ×ˢ Ioo (-v) v))) ∧
        IsOpen ((Subtype.val : frontier R → X) ⁻¹' (P.map '' (Q ×ˢ Ioo (-v) v)))) ∧
      PLDomain e P.cutCarrier ∧ IsCompact P.cutCarrier ∧
      Nonempty (ChartwisePLBall e P.cutCarrier (frontier P.cutCarrier)) ∧
      interior P.cutCarrier = interior R \ P.closedStrip ∧
      frontier P.cutCarrier = (frontier R \ P.openStrip) ∪ P.endDisks ∧
      P.closedStrip ∩ P.cutCarrier = P.endDisks ∧
      P.closedStrip ∪ P.cutCarrier = R ∧
      ∃ (H : (D ×ˢ Icc (a / 2) (p - a / 2) : Set E) ≃ₜ P.cutCarrier)
        (u : E → X),
        PolyhedralPLInCharts e u (D ×ˢ Icc (a / 2) (p - a / 2)) ∧
        (∀ z : (D ×ˢ Icc (a / 2) (p - a / 2) : Set E), u z = (H z : X)) ∧
        EqOn u (P.meridianCutFrontierMap a) (cubePrismBoundary (a / 2) (p - a / 2)) ∧
        (∀ z : (D ×ˢ Icc (a / 2) (p - a / 2) : Set E),
          u z ∈ frontier P.cutCarrier ↔ (z : E) ∈ cubePrismBoundary (a / 2) (p - a / 2)) ∧
        (∀ z ∈ D, u (z, a / 2) = P.map (z, 1 / 2)) ∧
        (∀ z ∈ D, u (z, p - a / 2) = P.map (z, -(1 / 2))) ∧
        ∀ z ∈ Q, ∀ t ∈ Icc (a / 2) (p - a / 2),
          u (z, t) = hamiltonMeridianCutAmbientMap (z, t) := by
  classical
  let : CompactSpace T := hamiltonSolidTorusCircleEquiv.symm.compactSpace
  let : T2Space T := hamiltonSolidTorusCircleEquiv.isEmbedding.t2Space
  have hR : IsCompact R := (isCompact_closedBall (0 : V2) 1).prod isCompact_univ
  obtain ⟨a, ha, hasmall, P, hPU, hmark, hopen, heK, hK, _,
    hint, hfront, hoverlap, hcover, _hne, s, Ls, HB, c, _hL, _hc, _hi, _hinside,
    _hbase, _hproperC, δ, _hδ, _hδsmall, _hopenC, _hlevel, _hlevelInt, Db, _hDbR,
    _hDb, _heq, _hcore, ⟨b⟩⟩ :=
    exists_source_meridian_cut_ball hI hd phi hphi F j hj hemb hDR hproper hrim hU hDU
  have hhalf : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip) :=
    (hopen (1 / 2) (by norm_num) (by norm_num)).1
  have hC := polyhedralPL_source_hamiltonComplementCylinder hd phi hphi F
    (half_pos ha) (by norm_num at hasmall ⊢; linarith : a / 2 < p / 2)
  obtain ⟨H, u, hu, hvalue, hboundary, hmem, hlower, hupper, hlateral⟩ :=
    P.exists_meridianCutPrism_extension hI.1 hR hhalf ha hasmall hmark hC b
  exact ⟨a, ha, hasmall, P, hPU, hmark, hopen, heK, hK, ⟨b⟩,
    hint, hfront, hoverlap, hcover, H, u, hu, hvalue, hboundary, hmem,
    hlower, hupper, hlateral⟩

end PoincareConjecture.M76
