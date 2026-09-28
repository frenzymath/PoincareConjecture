import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Disks.FrontierComparison









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1


def frontierBandPullback {X : Type*} [TopologicalSpace X] {N T : Set X}
    (E : ↥(frontier N) ≃ₜ ↥(frontier T)) (B : Set X) : Set X :=
  {x | ∃ hx : x ∈ frontier N, (E ⟨x, hx⟩ : X) ∈ B}

theorem frontierBandPullback_subset {X : Type*} [TopologicalSpace X] {N T B : Set X}
    (E : ↥(frontier N) ≃ₜ ↥(frontier T)) :
    frontierBandPullback E B ⊆ frontier N := fun _ hx => hx.choose


noncomputable def frontierBandPullbackHomeomorph
    {X : Type*} [TopologicalSpace X] {N T B : Set X}
    (E : ↥(frontier N) ≃ₜ ↥(frontier T)) (hB : B ⊆ frontier T) :
    B ≃ₜ frontierBandPullback E B where
  toFun x := ⟨E.symm ⟨x, hB x.property⟩, (E.symm ⟨x, hB x.property⟩).property,
    by simpa only [E.apply_symm_apply] using x.property⟩
  invFun x := ⟨E ⟨x, x.property.choose⟩, x.property.choose_spec⟩
  left_inv x := by
    apply Subtype.ext
    change (E (E.symm ⟨x, hB x.property⟩) : X) = x
    exact congrArg Subtype.val (E.apply_symm_apply _)
  right_inv x := by
    apply Subtype.ext
    change (E.symm (E ⟨x, x.property.choose⟩) : X) = x
    exact congrArg Subtype.val (E.symm_apply_apply _)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (E.symm.continuous.comp
      (continuous_subtype_val.subtype_mk _))
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (E.continuous.comp
      (continuous_subtype_val.subtype_mk _))


noncomputable def pulledBackBandCylinder
    {X : Type*} [TopologicalSpace X] {N T B : Set X}
    (E : ↥(frontier N) ≃ₜ ↥(frontier T)) (hB : B ⊆ frontier T)
    (c : ↥(Q ×ˢ I) ≃ₜ B) : ↥(Q ×ˢ I) ≃ₜ frontierBandPullback E B :=
  c.trans (frontierBandPullbackHomeomorph E hB)

theorem pulledBackBandCylinder_coe
    {X : Type*} [TopologicalSpace X] {N T B : Set X}
    (E : ↥(frontier N) ≃ₜ ↥(frontier T)) (hB : B ⊆ frontier T)
    (c : ↥(Q ×ˢ I) ≃ₜ B) (x : Q ×ˢ I) :
    (pulledBackBandCylinder E hB c x : X) =
      (E.symm ⟨c x, hB (c x).property⟩ : X) := rfl

theorem pulledBackBandCylinder_frontier_map
    {X : Type*} [TopologicalSpace X] {N T B : Set X}
    (E : ↥(frontier N) ≃ₜ ↥(frontier T)) (hB : B ⊆ frontier T)
    (c : ↥(Q ×ˢ I) ≃ₜ B) (x : Q ×ˢ I) :
    (E ⟨pulledBackBandCylinder E hB c x,
      frontierBandPullback_subset E (pulledBackBandCylinder E hB c x).property⟩ : X) = c x :=
  congrArg Subtype.val (E.apply_symm_apply _)


def cylinderBandInterior {X : Type*} [TopologicalSpace X] {B : Set X}
    (c : ↥(Q ×ˢ I) ≃ₜ B) : Set X :=
  {x | ∃ y : Q ×ˢ I, y.val.2 ∈ Ioo (-1 : ℝ) 1 ∧ (c y : X) = x}

theorem cylinderBandInterior_subset {X : Type*} [TopologicalSpace X] {B : Set X}
    (c : ↥(Q ×ˢ I) ≃ₜ B) : cylinderBandInterior c ⊆ B := by
  rintro x ⟨y, hy, rfl⟩
  exact (c y).property

theorem pulledBackBandCylinder_isCompact
    {X : Type*} [TopologicalSpace X] {N T B : Set X}
    (E : ↥(frontier N) ≃ₜ ↥(frontier T)) (hB : B ⊆ frontier T)
    (c : ↥(Q ×ˢ I) ≃ₜ B) : IsCompact (frontierBandPullback E B) := by
  let C := pulledBackBandCylinder E hB c
  have hc : IsCompact (Q ×ˢ I) := (isCompact_sphere (0 : V2) 1).prod isCompact_Icc
  let : CompactSpace ↥(Q ×ˢ I) := isCompact_iff_compactSpace.mp hc
  have hr : Set.range (fun x => (C x : X)) = frontierBandPullback E B := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩; exact (C y).property
    · intro hx
      exact ⟨C.symm ⟨x, hx⟩, congrArg Subtype.val (C.apply_symm_apply _)⟩
  rw [← hr]
  exact isCompact_range (continuous_subtype_val.comp C.continuous)

theorem pulledBackBandInterior_isOpen
    {X : Type*} [TopologicalSpace X] {N T B : Set X}
    (E : ↥(frontier N) ≃ₜ ↥(frontier T)) (hB : B ⊆ frontier T)
    (c : ↥(Q ×ˢ I) ≃ₜ B)
    (hopen : IsOpen ((Subtype.val : frontier T → X) ⁻¹' cylinderBandInterior c)) :
    IsOpen ((Subtype.val : frontier N → X) ⁻¹'
      cylinderBandInterior (pulledBackBandCylinder E hB c)) := by
  have heq : (Subtype.val : frontier N → X) ⁻¹'
      cylinderBandInterior (pulledBackBandCylinder E hB c) =
      E ⁻¹' ((Subtype.val : frontier T → X) ⁻¹' cylinderBandInterior c) := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      refine ⟨y, hy, ?_⟩
      have hh : E.symm ⟨c y, hB (c y).property⟩ = x := Subtype.ext hxy
      exact congrArg Subtype.val ((congrArg E hh).symm.trans (E.apply_symm_apply _)).symm
    · rintro ⟨y, hy, hxy⟩
      refine ⟨y, hy, ?_⟩
      have hh : (⟨c y, hB (c y).property⟩ : frontier T) = E x := Subtype.ext hxy
      exact congrArg Subtype.val ((congrArg E.symm hh).trans (E.symm_apply_apply _))
  rw [heq]
  exact hopen.preimage E.continuous


def cylinderZeroSection {X : Type*} [TopologicalSpace X] {B : Set X}
    (c : ↥(Q ×ˢ I) ≃ₜ B) : C(Q, B) where
  toFun x := c ⟨(x, 0), x.property, by norm_num⟩
  continuous_toFun := c.continuous.comp
    ((continuous_subtype_val.prodMk continuous_const).subtype_mk _)

theorem pulledBackBandZeroSection_frontier_map
    {X : Type*} [TopologicalSpace X] {N T B : Set X}
    (E : ↥(frontier N) ≃ₜ ↥(frontier T)) (hB : B ⊆ frontier T)
    (c : ↥(Q ×ˢ I) ≃ₜ B) (x : Q) :
    (E ⟨cylinderZeroSection (pulledBackBandCylinder E hB c) x,
      frontierBandPullback_subset E
        (cylinderZeroSection (pulledBackBandCylinder E hB c) x).property⟩ : X) =
      cylinderZeroSection c x :=
  pulledBackBandCylinder_frontier_map E hB c _




theorem exists_proper_disk_in_pulledBackBand
    {X α : Type*} [TopologicalSpace X] [T2Space X]
    (e : α → OpenPartialHomeomorph X V3) {N T B : Set X}
    (hN : PLDomain e N)
    (hinj : ∀ x : N, Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(N, X)) x))
    (E : ↥(frontier N) ≃ₜ ↥(frontier T))
    (hom : (⟨Subtype.val, continuous_subtype_val⟩ : C(frontier N, X)).Homotopic
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(frontier T, X)).comp ⟨E, E.continuous⟩))
    (hB : B ⊆ frontier T) (c : ↥(Q ×ˢ I) ≃ₜ B)
    (hopen : IsOpen ((Subtype.val : frontier T → X) ⁻¹' cylinderBandInterior c))
    (targetDisk : C(D, T))
    (hboundary : ∀ x : Q,
      (targetDisk ⟨x, sphere_subset_closedBall x.property⟩ : X) = cylinderZeroSection c x)
    (r : C(frontier T, Q))
    (hprojection : ∀ x : Q ×ˢ I, r ⟨c x, hB (c x).property⟩ =
      ⟨x.val.1, x.property.1⟩) :
    ∃ (j : V2 → X)
      (rim : C(Q, cylinderBandInterior (pulledBackBandCylinder E hB c))),
      PolyhedralPLInCharts e j D ∧ Topology.IsEmbedding (fun x : D => j x) ∧
      MapsTo j D N ∧ (∀ x : Q, j x = (rim x : X)) ∧
      (∀ x : D, j x ∈ frontier N ↔ (x : V2) ∈ Q) ∧
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        ((Dehn.squareRimLoop.map rim.continuous).map
          (ContinuousMap.inclusion
            (cylinderBandInterior_subset (pulledBackBandCylinder E hB c))).continuous)) ≠ 1 := by
  let C := pulledBackBandCylinder E hB c
  let F := cylinderBandInterior C
  have hFB : F ⊆ frontierBandPullback E B := cylinderBandInterior_subset C
  have hFN : F ⊆ frontier N := hFB.trans (frontierBandPullback_subset E)
  let gamma : C(Q, F) := {
    toFun := fun x => ⟨cylinderZeroSection C x,
      ⟨⟨(x, 0), x.property, by norm_num⟩, by norm_num, rfl⟩⟩
    continuous_toFun :=
      (continuous_subtype_val.comp (cylinderZeroSection C).continuous).subtype_mk _ }
  have hmark (x : Q) : (E (Set.inclusion hFN (gamma x)) : X) =
      cylinderZeroSection c x := pulledBackBandZeroSection_frontier_map E hB c x
  have hleft (x : Q) : r (E (Set.inclusion hFN (gamma x))) = x := by
    have heq : E (Set.inclusion hFN (gamma x)) =
        ⟨cylinderZeroSection c x, hB (cylinderZeroSection c x).property⟩ :=
      Subtype.ext (hmark x)
    rw [heq]
    exact hprojection ⟨(x, 0), x.property, by norm_num⟩
  obtain ⟨j, rim, hj, hi, hinside, hrim, hproper, hess⟩ :=
    exists_proper_marked_disk_of_frontier_comparison e hN hinj E hom F hFN
      (pulledBackBandInterior_isOpen E hB c hopen) gamma targetDisk
      (fun x => (hboundary x).trans (hmark x).symm) r hleft
  refine ⟨j, rim, hj, hi, hinside, hrim, hproper, ?_⟩
  let u : C(frontierBandPullback E B, Q) :=
    (r.comp ⟨E, E.continuous⟩).comp (ContinuousMap.inclusion (frontierBandPullback_subset E))
  intro hnull
  apply hess
  have hh := (Path.Homotopic.Quotient.eq.mp hnull).map u
  apply Path.Homotopic.Quotient.eq.mpr
  convert hh using 1 <;> rfl

end PoincareConjecture.M76.HamiltonIntervalTorus
