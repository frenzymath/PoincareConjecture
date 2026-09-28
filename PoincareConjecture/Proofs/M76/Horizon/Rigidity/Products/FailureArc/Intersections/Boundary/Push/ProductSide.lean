import PoincareConjecture.Proofs.M76.Rigidity.OriginalSmallDiskProduct
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Replacement.LocalOppositeStrip



set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "J" => Icc (0 : ℝ) 1

theorem exists_original_proper_disk_opposite_product
    {X ι B : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace B] [CompactSpace B] [PreconnectedSpace B]
    {e : ι → OpenPartialHomeomorph X V3} {R A Z O : Set X}
    (hR : IsCompact R) (he : PLDomain e R)
    {j : V2 → X} (hj : PolyhedralPLInCharts e j Disk) (hji : InjOn j Disk)
    (hjR : MapsTo j Disk R) (hjproper : ∀ x ∈ Disk, j x ∈ frontier R ↔ x ∈ Rim)
    (hO : IsOpen O) (hjO : j '' Disk ⊆ O)
    (p : B × J → X) (hp : Continuous p) (hpR : ∀ z, p z ∈ R)
    (hp0 : ∀ b, p (b, ⟨0, by norm_num⟩) ∈ j '' Disk)
    (hpzero : ∀ z, p z ∈ j '' Disk ↔ (z.2 : ℝ) = 0)
    {Q : Set Disk} (hQ : IsCompact Q) (hZ : IsClosed Z)
    (hQZ : ∀ q ∈ Q, j q ∉ Z) (hcover : A ⊆ (j '' Disk) ∪ range p ∪ Z) :
    ∃ (P : OriginalDiskProduct e R j) (δ : ℝ) (positive : Bool),
      MapsTo P.map (Disk ×ˢ I) O ∧ 0 < δ ∧ δ ≤ 1 / 2 ∧
      ∀ (q : Disk), q ∈ Q → ∀ t : I,
        (if positive then (t : ℝ) ∈ Ico (-δ) 0 else (t : ℝ) ∈ Ioc 0 δ) →
        P.map ((q : V2), (t : ℝ)) ∉ A := by
  let : CompactSpace Disk := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have hje : IsEmbedding (fun x : Disk ↦ j x) :=
    (hj.continuousOn.domRestrict.isClosedEmbedding
      (fun x y hxy ↦ Subtype.ext (hji x.property y.property hxy))).isEmbedding
  obtain ⟨P, hPO, hopen⟩ := exists_small_original_disk_product hR he hj hje hjR
    (fun x ↦ hjproper x x.property) hO hjO
  let f : Disk × I → R := fun z ↦ ⟨P.map ((z.1 : V2), (z.2 : ℝ)),
    P.inside ⟨z.1.property, z.2.property⟩⟩
  have hfc : Continuous f :=
    (P.polyhedral.continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
      (fun z ↦ ⟨z.1.property, z.2.property⟩)).subtype_mk _
  have hfi : Function.Injective f := by
    intro z w hzw
    have h := P.injective ⟨z.1.property, z.2.property⟩ ⟨w.1.property, w.2.property⟩
      (congrArg Subtype.val hzw)
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  let C := hfc.isClosedEmbedding hfi |>.isEmbedding.toHomeomorph
  let O' := (Subtype.val : R → X) ⁻¹' (P.map '' (Disk ×ˢ Ioo (-1 : ℝ) 1))
  have hO' : IsOpen O' := (hopen 1 (by norm_num) le_rfl).1
  have hOK : O' ⊆ range f := by
    rintro z ⟨⟨q, t⟩, ⟨hq, ht⟩, heq⟩
    exact ⟨(⟨q, hq⟩, ⟨t, ht.1.le, ht.2.le⟩), Subtype.ext heq⟩
  let S := (Subtype.val : R → X) ⁻¹' (j '' Disk)
  have hzero (z : Disk × I) : (C z : R) ∈ S ↔ (z.2 : ℝ) = 0 := by
    change P.map ((z.1 : V2), (z.2 : ℝ)) ∈ j '' Disk ↔ (z.2 : ℝ) = 0
    constructor
    · rintro ⟨q, hq, hqz⟩
      have hh := P.injective ⟨hq, by norm_num⟩ ⟨z.1.property, z.2.property⟩
        ((P.central q hq).trans hqz)
      exact (congrArg Prod.snd hh).symm
    · intro ht
      rw [ht, P.central _ z.1.property]
      exact mem_image_of_mem j z.1.property
  let pr : B × J → R := fun z ↦ ⟨p z, hpR z⟩
  have hpr : Continuous pr := hp.subtype_mk _
  have hpr0 (b : B) : pr (b, ⟨0, by norm_num⟩) ∈ O' := by
    obtain ⟨q, hq, hqp⟩ := hp0 b
    exact ⟨(q, 0), ⟨hq, by norm_num⟩, (P.central q hq).trans hqp⟩
  have hprzero (z : B × J) : pr z ∈ S ↔ (z.2 : ℝ) = 0 := hpzero z
  have hclosed : IsClosed ((Subtype.val : R → X) ⁻¹' Z) := hZ.preimage continuous_subtype_val
  have havoidzero (q : Disk) (hq : q ∈ Q) :
      (C (q, ⟨0, by norm_num⟩) : R) ∉ (Subtype.val : R → X) ⁻¹' Z := by
    change P.map ((q : V2), 0) ∉ Z
    rw [P.central q q.property]
    exact hQZ q hq
  have hcover' : (Subtype.val : R → X) ⁻¹' A ⊆
      S ∪ range pr ∪ (Subtype.val : R → X) ⁻¹' Z := by
    intro x hx
    rcases hcover hx with (hxS | hxp) | hxZ
    · exact Or.inl (Or.inl hxS)
    · obtain ⟨z, hzx⟩ := hxp
      exact Or.inl (Or.inr ⟨z, Subtype.ext hzx⟩)
    · exact Or.inr hxZ
  obtain ⟨δ, positive, hδ, hδhalf, havoid⟩ :=
    exists_local_opposite_strip_avoiding_surface C hO' hOK hzero pr hpr hpr0 hprzero
      hQ hclosed havoidzero hcover'
  exact ⟨P, δ, positive, hPO, hδ, hδhalf, havoid⟩

end PoincareConjecture.M76.Dehn.Annuli
