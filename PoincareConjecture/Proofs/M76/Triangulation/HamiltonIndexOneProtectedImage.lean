import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneDehnGeometry
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedCubeParameter
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionSphericalTransport










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

namespace HamiltonIndexOne

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "V" => ((Fin 1 ⊕ Fin 2) → ℝ)
local notation "W" => (ℝ × (ℝ × ℝ))
local notation "J" => Finset.univ.map (Function.Embedding.inl : Fin 1 ↪ Fin 1 ⊕ Fin 2)
local notation "D" => coordinateCylinder J



noncomputable def coverConjugate (A : V ≃ₜ V) : W ≃ₜ W :=
  coverCoordinates.symm.toHomeomorph.trans (A.trans coverCoordinates.toHomeomorph)


theorem coverConjugate_apply (A : V ≃ₜ V) (x : V) :
    coverConjugate A (coverCoordinates x) = coverCoordinates (A x) := by
  change coverCoordinates (A (coverCoordinates.symm (coverCoordinates x))) = _
  rw [coverCoordinates.symm_apply_apply]

private theorem conjugate_image (A : V ≃ₜ V) (P : Set V) :
    coverConjugate A '' (coverCoordinates '' P) = coverCoordinates '' (A '' P) := by
  rw [image_image, image_image]
  congr 1
  funext x
  exact coverConjugate_apply A x



theorem coverCoordinates_unit : coverCoordinates '' closedBall (0 : V) 1 =
    Icc (-1 : ℝ) 1 ×ˢ closedBall (0 : ℝ × ℝ) 1 := by
  have hball : coverCoordinates '' closedBall (0 : V) 1 = closedBall (0 : W) 1 := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      simpa only [mem_closedBall_zero_iff, coverCoordinates_norm] using hx
    · intro y hy
      refine ⟨coverCoordinates.symm y, ?_, coverCoordinates.apply_symm_apply y⟩
      have hn := coverCoordinates_norm (coverCoordinates.symm y)
      rw [coverCoordinates.apply_symm_apply] at hn
      exact mem_closedBall_zero_iff.mpr (hn.symm ▸ mem_closedBall_zero_iff.mp hy)
  rw [hball]
  ext x
  simp only [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff,
    Real.norm_eq_abs, mem_prod, mem_Icc, abs_le]



theorem coverConjugate_block_support (A : V ≃ₜ V)
    (hAout : ∀ x : V, 2 ≤ ‖x‖ → A x = x)
    (hArel : EqOn A id (Dᶜ ∪ frontier D)) :
    EqOn (coverConjugate A) id (interior squareBlock)ᶜ ∧
      coverConjugate A '' squareBlock = squareBlock := by
  let B0 : Set V := coverCoordinates ⁻¹' squareBlock
  have hsub : D ∩ closedBall (0 : V) 2 ⊆ B0 := by
    intro x hx
    refine ⟨abs_le.mp (hx.1 (Sum.inl 0)
      (Finset.mem_map.mpr ⟨0, Finset.mem_univ _, rfl⟩)), ?_⟩
    apply mem_closedBall_zero_iff.mpr
    change max ‖x (Sum.inr 0)‖ ‖x (Sum.inr 1)‖ ≤ 2
    exact max_le ((norm_le_pi_norm x _).trans (mem_closedBall_zero_iff.mp hx.2))
      ((norm_le_pi_norm x _).trans (mem_closedBall_zero_iff.mp hx.2))
  have hfix : EqOn A id (interior B0)ᶜ := by
    intro x hx
    by_cases hn : 2 ≤ ‖x‖
    · exact hAout x hn
    by_cases hxi : x ∈ interior D
    · have hi : x ∈ interior (D ∩ closedBall (0 : V) 2) := by
        rw [interior_inter]
        exact ⟨hxi, ball_subset_interior_closedBall (mem_ball_zero_iff.mpr (lt_of_not_ge hn))⟩
      exact (hx (interior_mono hsub hi)).elim
    by_cases hxd : x ∈ D
    · exact hArel (Or.inr ⟨subset_closure hxd, hxi⟩)
    · exact hArel (Or.inl hxd)
  have hphysical : EqOn (coverConjugate A) id (interior squareBlock)ᶜ := by
    intro x hx
    have hx' : coverCoordinates.symm x ∉ interior B0 := by
      change coverCoordinates.symm x ∉ interior (coverCoordinates.toHomeomorph ⁻¹' squareBlock)
      rw [← coverCoordinates.toHomeomorph.preimage_interior]
      change coverCoordinates (coverCoordinates.symm x) ∉ interior squareBlock
      rw [coverCoordinates.apply_symm_apply]
      exact hx
    change coverCoordinates (A (coverCoordinates.symm x)) = x
    rw [hfix hx']
    exact coverCoordinates.apply_symm_apply x
  exact ⟨hphysical, (coverConjugate A).image_eq_self_of_eqOn_compl
    (fun _ hx => hphysical (fun hi => hx (interior_subset hi)))⟩

private theorem unit_cube_ball_model :
    IsFinitePLBallPair W (closedBall (0 : V3) 1) (sphere (0 : V3) 1) := by
  have hmodel := (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)).prod
    (CoordinateHalfBoxes.base_ballPair (by norm_num : (0 : ℝ) < 1))
  let c : W ≃L[ℝ] V3 :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  obtain ⟨f, hf, hfb⟩ := hmodel.exists_cube_chart c
  apply hmodel.of_homeomorph sphere_subset_closedBall f.symm hf.symm
  intro x
  have h := hfb (f.symm x)
  rw [f.apply_symm_apply, frontier_closedBall _ one_ne_zero] at h
  exact h.symm

private theorem exists_unit_parameter_change :
    ∃ v : (Icc (-1 : ℝ) 1 ×ˢ sphere (0 : V2) 1) ≃ₜ annulusParameterSpace,
      v.IsFinitePL ∧ ∀ x : Icc (-1 : ℝ) 1 ×ˢ sphere (0 : V2) 1,
        (v x : V1 × V2) = (fun _ => x.val.1, x.val.2) := by
  let a : (V1 × V2) ≃ᴬ[ℝ] (ℝ × V2) :=
    ((ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 => ℝ)).prodCongr
      (ContinuousLinearEquiv.refl ℝ V2)).toContinuousAffineEquiv
  have hmem (x : V1 × V2) : a x ∈ Icc (-1 : ℝ) 1 ×ˢ sphere (0 : V2) 1 ↔
      x ∈ annulusParameterSpace := by
    change (x.1 0 ∈ Icc (-1 : ℝ) 1 ∧ x.2 ∈ sphere (0 : V2) 1) ↔ _
    change _ ↔ (x.1 ∈ closedBall (0 : V1) 1 ∧ x.2 ∈ sphere (0 : V2) 1)
    rw [mem_closedBall_zero_iff, ← boundedCoordinate_norm, Real.norm_eq_abs]
    exact and_congr abs_le.symm Iff.rfl
  have him : a '' annulusParameterSpace = Icc (-1 : ℝ) 1 ×ˢ sphere (0 : V2) 1 := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (hmem x).mpr hx
    · intro y hy
      exact ⟨a.symm y, (hmem _).mp ((a.apply_symm_apply y).symm ▸ hy), a.apply_symm_apply y⟩
  let u := (a.toHomeomorph.image annulusParameterSpace).trans (Homeomorph.setCongr him)
  obtain ⟨K, hK, hKs⟩ := exists_annulus_parameter_complex
  have hu : u.IsFinitePL :=
    ⟨a, ⟨K, hK, hKs, K.affineOnFaces_affine a.toContinuousAffineMap⟩, fun _ => rfl⟩
  exact ⟨u.symm, hu.symm, fun _ => rfl⟩

end HamiltonIndexOne

open HamiltonIndexOne

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "V" => ((Fin 1 ⊕ Fin 2) → ℝ)
local notation "W" => (ℝ × (ℝ × ℝ))
local notation "J" => Finset.univ.map (Function.Embedding.inl : Fin 1 ↪ Fin 1 ⊕ Fin 2)
local notation "D" => coordinateCylinder J

variable {L : Submodule ℤ V2} [DiscreteTopology L] {α γ β : Type*}
  {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3}
  {T : HamiltonProtectedDehnAnnulus L e}
  {region : HamiltonDehnEnclosingRegion (Fin 1) (Fin 2) L e T.surface}

local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L




structure HamiltonIndexOneProtectedImage
    (geometry : HamiltonIndexOneDehnGeometry L e T region) (A : V ≃ₜ V) where
  ball : IsFinitePLBallPair W (coverCoordinates '' (A '' geometry.Psum))
    ((coverCoordinates '' (A '' geometry.annulusSum)) ∪ squareAttachingDisks)
  subset_box : coverCoordinates '' (A '' geometry.Psum) ⊆ squareBlock
  annulus_compact : IsCompact (coverCoordinates '' (A '' geometry.annulusSum))
  boundary_contact : (coverCoordinates '' (A '' geometry.Psum)) ∩ frontier squareBlock =
    squareAttachingDisks
  annulus_contact : (coverCoordinates '' (A '' geometry.annulusSum)) ∩ frontier squareBlock =
    squareRims
  fixed_exterior : EqOn (coverConjugate A) id (interior squareBlock)ᶜ
  block_image : coverConjugate A '' squareBlock = squareBlock
  parameter : annulusParameterSpace ≃ₜ coverCoordinates '' (A '' geometry.annulusSum)
  parameter_PL : parameter.IsFinitePL
  parameter_eq : ∀ x : annulusParameterSpace,
    (parameter x : W) = coverCoordinates (A (geometry.annulusParameter x))
  unitParameter : (Icc (-1 : ℝ) 1 ×ˢ sphere (0 : V2) 1) ≃ₜ
    coverCoordinates '' (A '' geometry.annulusSum)
  unitParameter_PL : unitParameter.IsFinitePL
  unitParameter_eq : ∀ x : Icc (-1 : ℝ) 1 ×ˢ sphere (0 : V2) 1,
    (unitParameter x : W) = coverCoordinates (A (geometry.annulusParameter
      ⟨(fun _ => x.val.1, x.val.2), by
        refine ⟨mem_closedBall_zero_iff.mpr ?_, x.property.2⟩
        rw [← boundedCoordinate_norm, Real.norm_eq_abs]
        exact abs_le.mpr x.property.1⟩))
  tau : squareInnerAnnulus ≃ₜ coverCoordinates '' (A '' geometry.annulusSum)
  tau_PL : tau.IsFinitePL
  tau_parameter : ∀ x : annulusParameterSpace, ∀ hx : annulusCoordinates x ∈ squareInnerAnnulus,
    (tau ⟨annulusCoordinates x, hx⟩ : W) = parameter x
  tau_unitParameter : ∀ x : Icc (-1 : ℝ) 1 ×ˢ sphere (0 : V2) 1,
    ∀ hx : unitAnnulusCoordinates x ∈ squareInnerAnnulus,
      (tau ⟨unitAnnulusCoordinates x, hx⟩ : W) = unitParameter x
  tau_fix : ∀ x : squareInnerAnnulus, (x : W) ∈ squareRims → (tau x : W) = x
  core_compact : IsCompact (coverConjugate A ''
    (Icc (-1 : ℝ) 1 ×ˢ closedBall (0 : ℝ × ℝ) 1))
  core_subset : coverConjugate A '' (Icc (-1 : ℝ) 1 ×ˢ closedBall (0 : ℝ × ℝ) 1) ⊆
    coverCoordinates '' (A '' geometry.Psum)
  core_disjoint : Disjoint
    (coverConjugate A '' (Icc (-1 : ℝ) 1 ×ˢ closedBall (0 : ℝ × ℝ) 1))
    (coverCoordinates '' (A '' geometry.annulusSum))




theorem HamiltonIndexOneDehnGeometry.exists_protected_image_geometry
    (geometry : HamiltonIndexOneDehnGeometry L e T region)
    (ball : HamiltonMarkedProtectedBall (Fin 1) (Fin 2) L e region.region)
    (e' : γ → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3)
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (N : Set X)
    (hidentity : ChartwisePLOn e e' (ContinuousMap.id R)
      ((Subtype.val : R → X) ⁻¹' N))
    (g : LatticeHandle (Fin 1) (Fin 2) L ≃ₜ LatticeHandle (Fin 1) (Fin 2) L)
    (hg : ChartwisePLHomeomorph e' d
      (latticeHandleHomeomorphInDomain (Fin 1) (Fin 2) L g))
    (G : D ≃ₜ D)
    (hG : ∀ y, ((coordinateCylinderProduct (Fin 1) (Fin 2) (G y)).1,
        QuotientAddGroup.mk (coordinateCylinderProduct (Fin 1) (Fin 2) (G y)).2) =
      g ((coordinateCylinderProduct (Fin 1) (Fin 2) y).1,
        QuotientAddGroup.mk (coordinateCylinderProduct (Fin 1) (Fin 2) y).2))
    (p : OpenPartialHomeomorph V V) (hps : p.source = univ)
    (hp : LocallyPiecewiseAffineOn p p.source)
    (A : V ≃ₜ V) (hA : ∀ y : D, A (p y) = p (G y))
    (hPfix : EqOn p id geometry.Psum)
    (hPN : ∀ y ∈ geometry.Psum, latticeCoordinateProjection (Fin 1) (Fin 2) L y ∈ N)
    (hAout : ∀ x : V, 2 ≤ ‖x‖ → A x = x)
    (hArel : EqOn A id (Dᶜ ∪ frontier D)) :
    Nonempty (HamiltonIndexOneProtectedImage geometry A) := by
  classical
  let B : Set W := coverCoordinates '' (A '' geometry.Psum)
  let Z : Set W := coverCoordinates '' (A '' geometry.annulusSum)
  let H := coverConjugate A
  obtain ⟨hHfix, hHL⟩ := coverConjugate_block_support A hAout hArel
  have hHfront : EqOn H id (frontier squareBlock) := fun _ hx => hHfix hx.2
  have hcapFront : squareAttachingDisks ⊆ frontier squareBlock := by
    intro x hx
    exact (geometry.boundary_contact.symm.subset hx).2
  have hcapfix : EqOn H id squareAttachingDisks := fun _ hx => hHfront (hcapFront hx)
  have hcapImage : H '' squareAttachingDisks = squareAttachingDisks := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rwa [hcapfix hx]
    · intro x hx
      exact ⟨x, hx, hcapfix hx⟩
  have hcapmem (x : V) : coverCoordinates (A x) ∈ squareAttachingDisks ↔
      coverCoordinates x ∈ squareAttachingDisks := by
    have hh : H (coverCoordinates x) ∈ H '' squareAttachingDisks ↔
        coverCoordinates x ∈ squareAttachingDisks := H.injective.mem_set_image
    rw [hcapImage] at hh
    simpa only [H, coverConjugate_apply] using hh
  have hZmem (x : V) : coverCoordinates (A x) ∈ Z ↔
      coverCoordinates x ∈ coverCoordinates '' geometry.annulusSum := by
    change coverCoordinates (A x) ∈ coverCoordinates '' (A '' geometry.annulusSum) ↔ _
    rw [coverCoordinates.injective.mem_set_image, A.injective.mem_set_image,
      coverCoordinates.injective.mem_set_image]
  have hBsub : Z ∪ squareAttachingDisks ⊆ B := by
    apply union_subset (image_mono (image_mono geometry.annulus_subset))
    intro x hx
    have hxin : x ∈ coverCoordinates '' geometry.Psum :=
      (geometry.boundary_contact.symm.subset hx).1
    rw [← HamiltonIndexOne.conjugate_image A geometry.Psum]
    exact ⟨x, hxin, hcapfix hx⟩
  let u : closedBall (0 : V3) 1 ≃ₜ geometry.Psum :=
    ball.ball.parametrization.trans geometry.regionProjection.symm
  have huproject (x : closedBall (0 : V3) 1) :
      ball.ball.map x = latticeCoordinateProjection (Fin 1) (Fin 2) L (u x) := by
    rw [ball.ball.map_eq]
    have hq := geometry.regionProjection_eq (u x)
    rw [show geometry.regionProjection (u x) = ball.ball.parametrization x from
      geometry.regionProjection.apply_symm_apply (ball.ball.parametrization x)] at hq
    exact hq
  have huA : (u.trans (A.image geometry.Psum)).IsFinitePL :=
    protected_cube_image_isFinitePL e e' d hd N hidentity g hg G hG p hps hp A hA
      geometry.Psum geometry.in_cylinder hPfix hPN u ball.ball.map
      ball.ball.piecewiseAffine huproject
  let v : closedBall (0 : V3) 1 ≃ₜ B :=
    (u.trans (A.image geometry.Psum)).trans
      (coverCoordinates.toHomeomorph.image (A '' geometry.Psum))
  have hv : v.IsFinitePL := by
    obtain ⟨f, hf, hval⟩ := huA
    exact ⟨fun x => coverCoordinates (f x), hf.postcomp coverCoordinates.toContinuousAffineMap,
      fun x => congrArg coverCoordinates (hval x)⟩
  have hvboundary (x : closedBall (0 : V3) 1) :
      (v x : W) ∈ Z ∪ squareAttachingDisks ↔ (x : V3) ∈ sphere (0 : V3) 1 := by
    change (coverCoordinates (A (u x)) ∈ Z ∨
      coverCoordinates (A (u x)) ∈ squareAttachingDisks) ↔ _
    rw [hZmem, hcapmem]
    change coverCoordinates (u x) ∈ (coverCoordinates '' geometry.annulusSum) ∪
      squareAttachingDisks ↔ (x : V3) ∈ sphere (0 : V3) 1
    rw [← geometry.sphere_iff (u x) (u x).property,
      ← huproject, ball.ball.map_eq]
    exact ball.ball.boundary_eq x
  have hball : IsFinitePLBallPair W B (Z ∪ squareAttachingDisks) := by
    apply HamiltonIndexOne.unit_cube_ball_model.of_homeomorph hBsub v.symm hv.symm
    intro y
    have h := hvboundary (v.symm y)
    rw [v.apply_symm_apply] at h
    exact h
  obtain ⟨K, hK, hKs⟩ := exists_annulus_parameter_complex
  let uK : K.space ≃ₜ geometry.annulusSum :=
    (Homeomorph.setCongr hKs).trans geometry.annulusParameter
  have hfK : PolyhedralPLInCharts e T.map K.space := by rw [hKs]; exact T.piecewiseAffine
  have hfuK (x : K.space) : T.map x =
      latticeCoordinateProjection (Fin 1) (Fin 2) L (uK x) :=
    geometry.annulusParameter_projection (Homeomorph.setCongr hKs x)
  obtain ⟨f, hf, hval⟩ := protected_image_isFinitePL_of_quotient_parameterization
    e e' d hd N hidentity g hg G hG p hps hp A hA geometry.annulusSum
    (geometry.annulus_subset.trans geometry.in_cylinder) (hPfix.mono geometry.annulus_subset)
    (fun y hy => hPN y (geometry.annulus_subset hy)) K hK uK T.map hfK hfuK
  let param : annulusParameterSpace ≃ₜ Z :=
    (geometry.annulusParameter.trans (A.image geometry.annulusSum)).trans
      (coverCoordinates.toHomeomorph.image (A '' geometry.annulusSum))
  have hparam : param.IsFinitePL := by
    refine ⟨fun x => coverCoordinates (f x), ?_, ?_⟩
    · have hf' := hf.postcomp coverCoordinates.toContinuousAffineMap
      rwa [hKs] at hf'
    · intro x
      exact congrArg coverCoordinates (hval ⟨x, hKs.symm ▸ x.property⟩)
  obtain ⟨std, hstd, hstdval⟩ := exists_standard_annulus_parameter
  let tau : squareInnerAnnulus ≃ₜ Z := std.symm.trans param
  have htau : tau.IsFinitePL := hstd.symm.trans hparam
  have htauval (x : annulusParameterSpace) (hx : annulusCoordinates x ∈ squareInnerAnnulus) :
      (tau ⟨annulusCoordinates x, hx⟩ : W) = param x := by
    have heq : (⟨annulusCoordinates x, hx⟩ : squareInnerAnnulus) = std x :=
      Subtype.ext (hstdval x).symm
    change (param (std.symm ⟨annulusCoordinates x, hx⟩) : W) = _
    rw [heq, std.symm_apply_apply]
  have htaufix (x : squareInnerAnnulus) (hx : (x : W) ∈ squareRims) :
      (tau x : W) = x := by
    let z := std.symm x
    have hzx : annulusCoordinates z = (x : W) :=
      (hstdval z).symm.trans (congrArg Subtype.val (std.apply_symm_apply x))
    have hz : z.val.1 ∈ sphere (0 : V1) 1 :=
      (annulusCoordinates_mem_rims z).mp (hzx.symm ▸ hx)
    change coverCoordinates (A (geometry.annulusParameter z)) = (x : W)
    rw [← coverConjugate_apply, geometry.annulusParameter_boundary z hz, hzx]
    exact hcapfix ⟨hx.1, sphere_subset_closedBall hx.2⟩
  obtain ⟨unit, hunit, hunitval⟩ := HamiltonIndexOne.exists_unit_parameter_change
  have hcontact (P : Set V) (S : Set W)
      (hPS : (coverCoordinates '' P) ∩ frontier squareBlock = S) :
      (coverCoordinates '' (A '' P)) ∩ frontier squareBlock = S := by
    rw [← HamiltonIndexOne.conjugate_image A P]
    apply Subset.antisymm
    · rintro x ⟨⟨y, hy, hyx⟩, hxf⟩
      have heq : y = x := H.injective (hyx.trans (hHfront hxf).symm)
      exact hPS.subset ⟨heq ▸ hy, hxf⟩
    · intro x hx
      have hx' := hPS.symm.subset hx
      exact ⟨⟨x, hx'.1, hHfront hx'.2⟩, hx'.2⟩
  have hcoreImage : H '' (Icc (-1 : ℝ) 1 ×ˢ closedBall (0 : ℝ × ℝ) 1) =
      coverCoordinates '' (A '' closedBall (0 : V) 1) := by
    rw [← coverCoordinates_unit]
    exact HamiltonIndexOne.conjugate_image A _
  refine ⟨{
    ball := hball
    subset_box := ?_
    annulus_compact := (geometry.annulus_compact.image A.continuous).image
      coverCoordinates.continuous
    boundary_contact := hcontact _ _ geometry.boundary_contact
    annulus_contact := hcontact _ _ geometry.annulus_contact
    fixed_exterior := hHfix
    block_image := hHL
    parameter := param
    parameter_PL := hparam
    parameter_eq := fun _ => rfl
    unitParameter := unit.trans param
    unitParameter_PL := hunit.trans hparam
    unitParameter_eq := ?_
    tau := tau
    tau_PL := htau
    tau_parameter := htauval
    tau_unitParameter := ?_
    tau_fix := htaufix
    core_compact := (isCompact_Icc.prod (isCompact_closedBall _ _)).image H.continuous
    core_subset := ?_
    core_disjoint := ?_
  }⟩
  · rw [← HamiltonIndexOne.conjugate_image A geometry.Psum, ← hHL]
    exact image_mono geometry.subset_box
  · intro x
    change coverCoordinates (A (geometry.annulusParameter (unit x))) = _
    apply congrArg (fun z : annulusParameterSpace =>
      coverCoordinates (A (geometry.annulusParameter z)))
    exact Subtype.ext (hunitval x)
  · intro x hx
    have heq : annulusCoordinates (unit x) = unitAnnulusCoordinates x := by
      rw [hunitval x]
      rfl
    have h := htauval (unit x) (heq.symm ▸ hx)
    have hsub : (⟨annulusCoordinates (unit x), heq.symm ▸ hx⟩ : squareInnerAnnulus) =
        ⟨unitAnnulusCoordinates x, hx⟩ := Subtype.ext heq
    rwa [hsub] at h
  · rw [hcoreImage]
    exact image_mono (image_mono geometry.core_subset)
  · rw [hcoreImage]
    apply Set.disjoint_left.mpr
    rintro _ ⟨x, ⟨u, hu, rfl⟩, rfl⟩ ⟨y, ⟨v, hv, rfl⟩, heq⟩
    have hvu : v = u := A.injective (coverCoordinates.injective heq)
    exact Set.disjoint_left.mp geometry.core_disjoint hu (hvu ▸ hv)

end PoincareConjecture.M76
