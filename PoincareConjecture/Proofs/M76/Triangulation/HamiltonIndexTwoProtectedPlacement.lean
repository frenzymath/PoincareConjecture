import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexTwoDehnGeometry
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexTwoDiskParameter
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexTwoCoverPlacement
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedCubeParameter

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

open HamiltonIndexTwoStandard

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "W" => ((Fin 2 ⊕ Fin 1) → ℝ)
local notation "J" => Finset.univ.map (Function.Embedding.inl : Fin 2 ↪ Fin 2 ⊕ Fin 1)
local notation "D" => coordinateCylinder J
local notation "D3" => coordinateCylinder ({0, 1} : Finset (Fin 3))

variable {L : Submodule ℤ V1} [DiscreteTopology L] {α γ β : Type*}
  {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 2) (Fin 1) L) V3}
  {T : HamiltonProtectedDehnDisks L e}
  {region : HamiltonDehnEnclosingRegion (Fin 2) (Fin 1) L e (⋃ b, T.surface b)}

local notation "X" => LatticeHandleAmbient (Fin 2) (Fin 1) L
local notation "R" => latticeHandleDomain (Fin 2) (Fin 1) L

theorem HamiltonIndexTwoDehnGeometry.exists_protected_cover_placement
    (geometry : HamiltonIndexTwoDehnGeometry L e T region)
    (ball : HamiltonMarkedProtectedBall (Fin 2) (Fin 1) L e region.region)
    (e' : γ → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3)
    (hd : StandardLatticeHandleAtlas (Fin 2) (Fin 1) L d)
    (N : Set X)
    (hidentity : ChartwisePLOn e e' (ContinuousMap.id R)
      ((Subtype.val : R → X) ⁻¹' N))
    (g : LatticeHandle (Fin 2) (Fin 1) L ≃ₜ LatticeHandle (Fin 2) (Fin 1) L)
    (hg : ChartwisePLHomeomorph e' d
      (latticeHandleHomeomorphInDomain (Fin 2) (Fin 1) L g))
    (G : D ≃ₜ D)
    (hG : ∀ y, ((coordinateCylinderProduct (Fin 2) (Fin 1) (G y)).1,
        QuotientAddGroup.mk (coordinateCylinderProduct (Fin 2) (Fin 1) (G y)).2) =
      g ((coordinateCylinderProduct (Fin 2) (Fin 1) y).1,
        QuotientAddGroup.mk (coordinateCylinderProduct (Fin 2) (Fin 1) y).2))
    (p : OpenPartialHomeomorph W W) (hps : p.source = univ)
    (hp : LocallyPiecewiseAffineOn p p.source)
    (A : W ≃ₜ W) (hA : ∀ y : D, A (p y) = p (G y))
    (hPfix : EqOn p id geometry.Psum)
    (hPN : ∀ y ∈ geometry.Psum, latticeCoordinateProjection (Fin 2) (Fin 1) L y ∈ N)
    (hAout : ∀ x : W, 2 ≤ ‖x‖ → A x = x)
    (hArel : EqOn A id (Dᶜ ∪ frontier D)) :
    ∃ Q : W ≃ₜ W,
      FinitePiecewiseAffineOn Q (closedBall (0 : W) 1) ∧
      (∀ x : W, 2 ≤ ‖x‖ → Q x = x) ∧
      EqOn Q id (Dᶜ ∪ frontier D) ∧
      MapsTo Q (closedBall (0 : W) 1) (A '' geometry.Psum) := by
  classical
  let pi := latticeCoordinateProjection (Fin 2) (Fin 1) L
  let P3 : Set V3 := coverCoordinates '' geometry.Psum
  let delta3 (b : Bool) : Set V3 := coverCoordinates '' geometry.deltaSum b
  let B3 : Set V3 := (side ∪ delta3 false) ∪ delta3 true
  let A3 := coverCoordinates.symm.toHomeomorph.trans
    (A.trans coverCoordinates.toHomeomorph)
  obtain ⟨hA3out, hA3rel, hA3image⟩ :=
    cover_conjugate_conditions A hAout hArel geometry.Psum
  have hboxfix : EqOn A3 id (interior (Icc lowerBound upperBound))ᶜ :=
    fixes_box_exterior A3 hA3out hA3rel
  have hsidefix (x : V3) (hx : x ∈ side) : A3 x = x := by
    have hfront : x ∈ frontier (Icc lowerBound upperBound) :=
      frame.frontier_eq.symm.subset (Or.inl (Or.inl hx))
    exact hboxfix hfront.2
  have hsideImage : A3 '' side = side := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rwa [hsidefix x hx]
    · intro x hx
      exact ⟨x, hx, hsidefix x hx⟩
  have hBsub : B3 ⊆ P3 := by
    rintro x ((hx | hx) | hx)
    · exact (geometry.boundary_contact.symm.subset hx).1
    · exact image_mono (geometry.disk_subset false) hx
    · exact image_mono (geometry.disk_subset true) hx
  let u : closedBall (0 : V3) 1 ≃ₜ geometry.Psum :=
    ball.ball.parametrization.trans geometry.regionProjection.symm
  have huproject (x : closedBall (0 : V3) 1) : ball.ball.map x = pi (u x) := by
    rw [ball.ball.map_eq]
    have hq := geometry.regionProjection_eq (u x)
    rw [show geometry.regionProjection (u x) = ball.ball.parametrization x from
      geometry.regionProjection.apply_symm_apply (ball.ball.parametrization x)] at hq
    exact hq
  have huPL : (u.trans (A.image geometry.Psum)).IsFinitePL :=
    protected_cube_image_isFinitePL e e' d hd N hidentity g hg G hG p hps hp A hA
      geometry.Psum geometry.in_cylinder hPfix hPN u ball.ball.map
        ball.ball.piecewiseAffine huproject
  have hframePL {n : ℕ} {B : Set W}
      (v : closedBall (0 : Fin n → ℝ) 1 ≃ₜ B)
      (hv : (v.trans (A.image B)).IsFinitePL) :
      ((v.trans (coverCoordinates.toHomeomorph.image B)).trans
        (A3.image (coverCoordinates '' B))).IsFinitePL := by
    obtain ⟨f, hf, hval⟩ := hv
    refine ⟨fun x => coverCoordinates (f x),
      hf.postcomp coverCoordinates.toContinuousAffineMap, ?_⟩
    intro x
    change coverCoordinates (A (coverCoordinates.symm (coverCoordinates (v x)))) =
      coverCoordinates (f x)
    rw [coverCoordinates.symm_apply_apply]
    exact congrArg coverCoordinates (hval x)
  let u3 : closedBall (0 : V3) 1 ≃ₜ P3 :=
    u.trans (coverCoordinates.toHomeomorph.image geometry.Psum)
  have huBoundary (x : closedBall (0 : V3) 1) :
      (u3 x : V3) ∈ B3 ↔ (x : V3) ∈ sphere (0 : V3) 1 := by
    change coverCoordinates (u x) ∈ B3 ↔ _
    rw [← geometry.sphere_iff (u x) (u x).property]
    change pi (u x) ∈ frontier region.region ↔ (x : V3) ∈ sphere (0 : V3) 1
    rw [← huproject, ball.ball.map_eq]
    exact ball.ball.boundary_eq x
  have hballPair : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (A3 '' P3)
      ((side ∪ A3 '' delta3 false) ∪ A3 '' delta3 true) := by
    have hh := protected_image_three_ball hBsub u3 huBoundary A3 (hframePL u huPL)
    simpa only [B3, image_union, hsideImage] using hh
  have hdPL (b : Bool) :
      ((geometry.diskParameter b).trans (A.image (geometry.deltaSum b))).IsFinitePL :=
    protected_cube_image_isFinitePL e e' d hd N hidentity g hg G hG p hps hp A hA
      (geometry.deltaSum b) ((geometry.disk_subset b).trans geometry.in_cylinder)
      (hPfix.mono (geometry.disk_subset b))
      (fun y hy => hPN y (geometry.disk_subset b hy)) (geometry.diskParameter b)
      (T.map b) (T.piecewiseAffine b) (geometry.diskParameter_projection b)
  let v3 (b : Bool) : closedBall (0 : V2) 1 ≃ₜ A3 '' delta3 b :=
    ((geometry.diskParameter b).trans
      (coverCoordinates.toHomeomorph.image (geometry.deltaSum b))).trans
        (A3.image (delta3 b))
  have hv3 (b : Bool) : (v3 b).IsFinitePL := hframePL (geometry.diskParameter b) (hdPL b)
  choose std hstd hstdval hstdboundary using exists_standard_disk_parameter
  let diskMap (b : Bool) : source.disk b ≃ₜ A3 '' delta3 b :=
    (std b).symm.trans (v3 b)
  have hdiskMap (b : Bool) : (diskMap b).IsFinitePL := (hstd b).symm.trans (hv3 b)
  have hdiskFix (b : Bool) (y : source.disk b) (hy : (y : V3) ∈ rim b) :
      (diskMap b y : V3) = y := by
    let x := (std b).symm y
    have hxy : (std b x : V3) = y := congrArg Subtype.val ((std b).apply_symm_apply y)
    have hxs : (x : V2) ∈ sphere (0 : V2) 1 :=
      (hstdboundary b x).mp (hxy.symm ▸ hy)
    have hpoint : coverCoordinates (geometry.diskParameter b x) = (y : V3) :=
      (geometry.diskParameter_boundary b x hxs).trans ((hstdval b x).symm.trans hxy)
    change A3 (coverCoordinates (geometry.diskParameter b x)) = (y : V3)
    rw [hpoint]
    exact hsidefix y ((source.disk_side b).symm.subset hy).2
  have hdiskPair (b : Bool) : IsFinitePLBallPair (ℝ × ℝ) (A3 '' delta3 b) (rim b) :=
    protected_image_disk_pair (source.diskBall b) (diskMap b) (hdiskMap b) (hdiskFix b)
  have hdis : Disjoint (delta3 false) (delta3 true) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
    have hyx : y = x := coverCoordinates.injective heq
    exact Set.disjoint_left.mp geometry.disks_disjoint hx (hyx ▸ hy)
  obtain ⟨Q, hQPL, hQout, hQrel, hplace⟩ := exists_supported_placement_in_image P3 delta3
    geometry.subset_box geometry.boundary_contact
    (fun b => image_mono (geometry.disk_subset b)) geometry.disk_side hdis
    A3 hA3out hA3rel hballPair hdiskPair diskMap hdiskMap hdiskFix
  apply exists_cover_supported_placement geometry.Psum A Q hQPL hQout hQrel
  intro x hx
  rw [← hA3image]
  exact hplace hx

end PoincareConjecture.M76
