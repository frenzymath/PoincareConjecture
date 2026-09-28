import PoincareConjecture.Proofs.M76.Rigidity.OriginalPeriodPL
import PoincareConjecture.Proofs.M76.Rigidity.OriginalPeriodImage
import PoincareConjecture.Proofs.M76.Rigidity.OriginalPeriodFibers
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.QuotientFibersHomeomorph
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.ClosedPeriodCut










set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "W" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

private instance : Fact (0 < p) := ⟨by norm_num⟩



theorem exists_period_homeomorph
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {N : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e N j) (he : PLDomain e N) (hN : IsCompact N)
    (hopen : IsOpen ((Subtype.val : N → X) ⁻¹' P.openStrip))
    {w : ℝ} (hw : 0 < w) (hgap : w / 2 < p - w / 2)
    (H : (D ×ˢ Icc (w / 2) (p - w / 2) : Set W) ≃ₜ P.cutCarrier)
    (u : W → X)
    (hu : PolyhedralPLInCharts e u (D ×ˢ Icc (w / 2) (p - w / 2)))
    (hvalue : ∀ z : (D ×ˢ Icc (w / 2) (p - w / 2) : Set W), u z = (H z : X))
    (hlower : ∀ z ∈ D, u (z, w / 2) = P.map (z, (1 / 2 : ℝ)))
    (hupper : ∀ z ∈ D, u (z, p - w / 2) = P.map (z, -(1 / 2 : ℝ))) :
    ∃ G : (D × C) ≃ₜ N,
      PolyhedralPLInCharts e (P.periodCutMap w p u) (D ×ˢ Icc 0 p) ∧
      (∀ z : D, ∀ t ∈ Icc (0 : ℝ) p,
        (G (z, (t : C)) : X) = P.periodCutMap w p u (z, t)) ∧
      (∀ z : D, (G (z, 0) : X) = j z) ∧
      (∀ z : D, (G (z, ((w / 2 : ℝ) : C)) : X) = P.map (z, (1 / 2 : ℝ))) ∧
      ∀ z : D, (G (z, ((p - w / 2 : ℝ) : C)) : X) = P.map (z, -(1 / 2 : ℝ)) := by
  have hPL := P.polyhedral_periodCutMap he hw hgap u hu hlower hupper
  have hcover : P.closedStrip ∪ P.cutCarrier = N := (P.cut_geometry hN hopen).2.2.2.2.1
  have himage := P.image_periodCutMap hw hgap H u hvalue hlower hupper hcover
  let S := (D ×ˢ Icc (0 : ℝ) p : Set W)
  have hS : IsCompact S := (isCompact_closedBall (0 : V2) 1).prod isCompact_Icc
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let q : C(S, D × C) := {
    toFun := fun z => (⟨z.val.1, z.property.1⟩, (z.val.2 : C))
    continuous_toFun :=
      ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
        ((AddCircle.continuous_mk' p).comp (continuous_snd.comp continuous_subtype_val)) }
  have hqsurj : Function.Surjective q := by
    intro x
    let t := AddCircle.equivIco p 0 x.2
    have ht : (t : ℝ) ∈ Icc (0 : ℝ) p := by
      exact ⟨t.property.1, by simpa only [zero_add] using t.property.2.le⟩
    refine ⟨⟨((x.1 : V2), (t : ℝ)), x.1.property, ht⟩, ?_⟩
    apply Prod.ext
    · rfl
    · exact AddCircle.coe_equivIco
  let r : C(S, N) := {
    toFun := fun z => ⟨P.periodCutMap w p u z, himage.subset ⟨z, z.property, rfl⟩⟩
    continuous_toFun :=
      (continuousOn_iff_continuous_domRestrict.mp hPL.continuousOn).subtype_mk _ }
  have hrsurj : Function.Surjective r := by
    intro x
    obtain ⟨z, hz, hzx⟩ := himage.symm.subset x.property
    exact ⟨⟨z, hz⟩, Subtype.ext hzx⟩
  have hq : Topology.IsQuotientMap q :=
    q.continuous.isClosedMap.isQuotientMap q.continuous hqsurj
  have hr : Topology.IsQuotientMap r :=
    r.continuous.isClosedMap.isQuotientMap r.continuous hrsurj
  have hfib (z z' : S) : q z = q z' ↔ r z = r z' := by
    have hqeq : q z = q z' ↔ z.val.1 = z'.val.1 ∧
        ((z.val.2 : C) = (z'.val.2 : C)) := by
      constructor
      · intro h
        exact ⟨congrArg (fun x : D × C => (x.1 : V2)) h, congrArg Prod.snd h⟩
      · rintro ⟨hf, ht⟩
        exact Prod.ext (Subtype.ext hf) ht
    have hreq : r z = r z' ↔ P.periodCutMap w p u z = P.periodCutMap w p u z' :=
      Subtype.ext_iff
    rw [hqeq, hreq, AddCircle.coe_eq_coe_iff_eq_or_endpoints z.property.2 z'.property.2,
      P.periodCutMap_eq_iff hw hgap H u hvalue hlower hupper z.property z'.property]
  obtain ⟨G, hG⟩ := hq.exists_homeomorph_of_fibers hr hfib
  have hwhole (z : D) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) p) :
      (G (z, (t : C)) : X) = P.periodCutMap w p u (z, t) :=
    congrArg Subtype.val (hG ⟨(z, t), z.property, ht⟩)
  refine ⟨G, hPL, hwhole, ?_, ?_, ?_⟩
  · intro z
    exact (hwhole z 0 (by norm_num)).trans (P.periodCutMap_endpoints hw hgap u z z.property).1
  · intro z
    have ht : w / 2 ∈ Icc (0 : ℝ) p := ⟨by linarith, by linarith⟩
    rw [hwhole z _ ht, P.periodCutMap_middle hw hgap u hlower hupper
      (show ((z : V2), w / 2) ∈ D ×ˢ Icc (w / 2) (p - w / 2) from
        ⟨z.property, le_rfl, hgap.le⟩)]
    exact hlower z z.property
  · intro z
    have ht : p - w / 2 ∈ Icc (0 : ℝ) p := ⟨by linarith, by linarith⟩
    rw [hwhole z _ ht, P.periodCutMap_middle hw hgap u hlower hupper
      (show ((z : V2), p - w / 2) ∈ D ×ˢ Icc (w / 2) (p - w / 2) from
        ⟨z.property, hgap.le, le_rfl⟩)]
    exact hupper z z.property

end PoincareConjecture.M76.OriginalDiskProduct
