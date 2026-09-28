import PoincareConjecture.Proofs.M76.Rigidity.MarkedMeridianStrip
import PoincareConjecture.Proofs.M76.Rigidity.SourceMeridianMarkedProduct









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "X" => LatticeHandleAmbient (Fin 2) (Fin 1) L
local notation "R" => latticeHandleDomain (Fin 2) (Fin 1) L
local notation "H" => LatticeHandle (Fin 2) (Fin 1) L
local notation "B" => latticeHandleBoundary (Fin 2) (Fin 1) L
local notation "p" => (4 * (128 : ℝ))




theorem exists_source_meridian_retained_cylinder
    {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3}
    (he : PLDomain e R) (hd : StandardLatticeHandleAtlas (Fin 2) (Fin 1) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 2) (Fin 1) L phi))
    (F : (ContinuousMap.id H).HomotopyRel phi B)
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
      PolyhedralPLInCharts e hamiltonMeridianCutAmbientMap
        (Q ×ˢ Icc (a / 2) (p - a / 2)) ∧
      InjOn hamiltonMeridianCutAmbientMap (Q ×ˢ Icc (a / 2) (p - a / 2)) ∧
      hamiltonMeridianCutAmbientMap '' (Q ×ˢ Icc (a / 2) (p - a / 2)) =
        frontier R \ P.openStrip ∧
      (∀ z ∈ Q, P.map (z, (1 / 2 : ℝ)) =
        hamiltonMeridianCutAmbientMap (z, a / 2)) ∧
      (∀ z ∈ Q, P.map (z, -(1 / 2 : ℝ)) =
        hamiltonMeridianCutAmbientMap (z, p - a / 2)) ∧
      ∃ h : (Q ×ˢ Icc (a / 2) (p - a / 2) : Set (V2 × ℝ)) ≃ₜ
          (frontier R \ P.openStrip : Set X),
        ∀ z, (h z : X) = hamiltonMeridianCutAmbientMap z := by
  obtain ⟨a, ha, hasmall, P, hPU, hmark, hopen⟩ :=
    exists_source_meridian_marked_product he hd phi hphi F j hj hemb hDR hproper hrim hU hDU
  have hapos : 0 < a / 2 := by linarith
  have happ : a / 2 < p / 2 := by norm_num at hasmall ⊢; linarith
  have himage := P.marked_meridian_retained_frontier ha hasmall hmark
  obtain ⟨hplus, hminus⟩ := P.marked_meridian_cap_rims hmark
  obtain ⟨h, hval⟩ := exists_hamiltonComplementCylinder_homeomorph hapos happ
  have htarget := (image_hamiltonComplementCylinder hapos happ).symm.trans himage
  refine ⟨a, ha, hasmall, P, hPU, hmark, hopen,
    polyhedralPL_source_hamiltonComplementCylinder hd phi hphi F hapos happ,
    injOn_hamiltonComplementCylinder hapos, himage, hplus, hminus,
    h.trans (Homeomorph.setCongr htarget), ?_⟩
  exact hval

end PoincareConjecture.M76
