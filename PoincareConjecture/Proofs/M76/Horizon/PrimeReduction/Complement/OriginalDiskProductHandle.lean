import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.OriginalDiskCutCollars
import PoincareConjecture.Proofs.M76.Wall.PLDomainLocalPathConnected
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.ProductHandleNotPuncturedSphere

set_option autoImplicit false
open Set Metric Geometry
open scoped unitInterval

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Sphere" => Geometry.CubicalThreeSphere.sphere

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}

theorem OriginalDiskProduct.exists_closedStrip_product
    (P : OriginalDiskProduct e R j) :
    ∃ C : (Disk × unitInterval) ≃ₜ P.closedStrip,
      (∀ z, (C z : X) = P.map (z.1, (z.2 : ℝ) - 1 / 2)) ∧
      ∀ z, (C z : X) ∈ P.endDisks ↔ z.2 = 0 ∨ z.2 = 1 := by
  classical
  have hfull (z : Disk × unitInterval) :
      ((z.1 : V2), (z.2 : ℝ) - 1 / 2) ∈ Disk ×ˢ Icc (-1 : ℝ) 1 :=
    ⟨z.1.property, by constructor <;> linarith [z.2.property.1, z.2.property.2]⟩
  let f : Disk × unitInterval → P.closedStrip := fun z =>
    ⟨P.map (z.1, (z.2 : ℝ) - 1 / 2), ⟨((z.1 : V2), (z.2 : ℝ) - 1 / 2),
      ⟨z.1.property, by constructor <;> linarith [z.2.property.1, z.2.property.2]⟩, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro z w h
      have hh := P.injective (hfull z) (hfull w) (congrArg Subtype.val h)
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst hh)
      · apply Subtype.ext
        have ht := congrArg Prod.snd hh
        dsimp at ht
        linarith
    · rintro ⟨x, p, hp, rfl⟩
      refine ⟨(⟨p.1, hp.1⟩, ⟨p.2 + 1 / 2,
        by constructor <;> linarith [hp.2.1, hp.2.2]⟩), ?_⟩
      apply Subtype.ext
      change P.map (p.1, p.2 + 1 / 2 - 1 / 2) = P.map p
      simp
  have hfc : Continuous f := by
    apply Continuous.subtype_mk
    exact P.polyhedral.continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        ((continuous_subtype_val.comp continuous_snd).sub continuous_const)) hfull
  let C : (Disk × unitInterval) ≃ₜ P.closedStrip :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hf) hfc
  refine ⟨C, fun _ => rfl, ?_⟩
  intro z
  change P.map ((z.1 : V2), (z.2 : ℝ) - 1 / 2) ∈ P.endDisks ↔ _
  constructor
  · rintro ⟨w, hw, hwz⟩
    have hwt : w.2 = -(1 / 2 : ℝ) ∨ w.2 = 1 / 2 := hw.2
    have hwfull : w ∈ Disk ×ˢ Icc (-1 : ℝ) 1 := by
      refine ⟨hw.1, ?_⟩
      rcases hwt with h | h <;> rw [h] <;> norm_num
    have ht := congrArg Prod.snd (P.injective hwfull (hfull z) hwz)
    dsimp at ht
    rcases hwt with h | h
    · left
      apply Subtype.ext
      change (z.2 : ℝ) = 0
      linarith
    · right
      apply Subtype.ext
      change (z.2 : ℝ) = 1
      linarith
  · intro hz
    refine ⟨((z.1 : V2), (z.2 : ℝ) - 1 / 2), ⟨z.1.property, ?_⟩, rfl⟩
    rcases hz with h | h <;> rw [h] <;> norm_num

theorem OriginalDiskProduct.not_homeomorph_punctured_sphere_of_connected_cut
    (P : OriginalDiskProduct e R j) (hR : IsCompact R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip))
    (hPL : PLDomain e P.cutCarrier) (hconn : IsConnected P.cutCarrier)
    {κ : Type*} [Finite κ] (D B : κ → Set V4)
    (hD : ∀ i, IsFinitePLBallPair V3 (D i) (B i))
    (hDS : ∀ i, D i ⊆ Sphere)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (hholes : ∀ i, IsOpen ((Subtype.val : Sphere → V4) ⁻¹' (D i \ B i))) :
    ¬ Nonempty (R ≃ₜ (Sphere \ ⋃ i, D i \ B i : Set V4)) := by
  obtain ⟨C, _, hends⟩ := P.exists_closedStrip_product
  obtain ⟨hc, _, _, hoverlap, hcover, _⟩ := P.cut_geometry hR hopen
  let : Nonempty Disk := ⟨⟨0, mem_closedBall_self zero_le_one⟩⟩
  let : LocallyPathConnectedSpace P.cutCarrier := hPL.locallyPathConnectedSpace
  let : ConnectedSpace P.cutCarrier := isConnected_iff_connectedSpace.mp hconn
  let : PathConnectedSpace P.cutCarrier := PathConnectedSpace.of_locallyPathConnectedSpace
  have hpath : IsPathConnected P.cutCarrier :=
    isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  have hatt (z : Disk × unitInterval) :
      (C z : X) ∈ P.cutCarrier ↔ z.2 = 0 ∨ z.2 = 1 := by
    rw [← hends]
    constructor
    · intro hz
      exact hoverlap.subset ⟨(C z).property, hz⟩
    · intro hz
      exact (hoverlap.symm.subset hz).2
  have hno := Poincare.Topology.not_nonempty_homeomorph_punctured_sphere_of_product_handle
    hc.isClosed (P.isCompact_closed_strip (by norm_num : (1 / 2 : ℝ) ≤ 1)).isClosed
    hpath C hatt D B hD hDS hdis hholes
  change ¬ Nonempty ((P.cutCarrier ∪ P.closedStrip : Set X) ≃ₜ
    (Sphere \ ⋃ i, D i \ B i : Set V4)) at hno
  rw [union_comm, hcover] at hno
  exact hno

theorem exists_original_disk_cut_with_product_obstruction
    {U : Set X} (hR : IsCompact R) (he : PLDomain e R)
    (hj : PolyhedralPLInCharts e j Disk)
    (hemb : Topology.IsEmbedding (fun z : Disk => j z))
    (hDR : MapsTo j Disk R)
    (hproper : ∀ z : Disk, j z ∈ frontier R ↔ (z : V2) ∈ sphere 0 1)
    (hU : IsOpen U) (hDU : j '' Disk ⊆ U)
    {κ : Type*} [Finite κ] (D B : κ → Set V4)
    (hD : ∀ i, IsFinitePLBallPair V3 (D i) (B i))
    (hDS : ∀ i, D i ⊆ Sphere)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (hholes : ∀ i, IsOpen ((Subtype.val : Sphere → V4) ⁻¹' (D i \ B i))) :
    ∃ (P : OriginalDiskProduct e R j) (C : (Disk × unitInterval) ≃ₜ P.closedStrip),
      MapsTo P.map (Disk ×ˢ Icc (-1 : ℝ) 1) U ∧
      PLDomain e P.cutCarrier ∧ IsCompact P.cutCarrier ∧
      P.closedStrip ∩ P.cutCarrier = P.endDisks ∧ P.closedStrip ∪ P.cutCarrier = R ∧
      (∀ z, (C z : X) = P.map (z.1, (z.2 : ℝ) - 1 / 2)) ∧
      (∀ z, (C z : X) ∈ P.cutCarrier ↔ z.2 = 0 ∨ z.2 = 1) ∧
      (IsConnected P.cutCarrier →
        ¬ Nonempty (R ≃ₜ (Sphere \ ⋃ i, D i \ B i : Set V4))) := by
  obtain ⟨P, hsmall, hopen, hPL, hc, _, _, ho, hu, _, _⟩ :=
    exists_original_disk_cut_domain_with_collars hR he hj hemb hDR hproper hU hDU
  obtain ⟨C, hC, hends⟩ := P.exists_closedStrip_product
  refine ⟨P, C, hsmall, hPL, hc, ho, hu, hC, ?_, ?_⟩
  · intro z
    rw [← hends]
    exact ⟨fun hz => ho.subset ⟨(C z).property, hz⟩, fun hz => (ho.symm.subset hz).2⟩
  · intro hconn
    exact P.not_homeomorph_punctured_sphere_of_connected_cut hR hopen hPL hconn
      D B hD hDS hdis hholes

end PoincareConjecture.M76
