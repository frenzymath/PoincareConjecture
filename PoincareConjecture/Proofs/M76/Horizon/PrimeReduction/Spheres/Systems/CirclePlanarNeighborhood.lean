import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.MemberCircleCut
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallNormalization
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionBallInterior
import PoincareConjecture.Proofs.M76.Mathlib.CoordinateHalfBoxes

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Sphere" => sphere (0 : V3) 1
local notation "Square" => CoordinateHalfBoxes.base 1
local notation "SquareRim" => CoordinateHalfBoxes.baseBoundary 1

theorem ChartwisePLSphere.exists_circle_planar_neighborhood
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) {n : ℕ} (R : Polygon V3 (n + 3))
    (hR : R.HasSimplicialEdges) (hRi : Function.Injective R)
    {d : Set V3} (hd : IsFinitePLBallPair P2 d (R.boundary ℝ)) (hdS : d ⊆ Sphere) :
    ∃ (p : V3) (A q : Set V3) (F : A ≃ₜ Square),
      p ∈ d \ R.boundary ℝ ∧ p ∉ A ∧ IsFinitePLBallPair P2 A q ∧ A ⊆ Sphere ∧
      R.boundary ℝ ⊆ A \ q ∧
      IsOpen ((Subtype.val : Sphere → V3) ⁻¹' (A \ q)) ∧ F.IsFinitePL ∧
      (∀ x : A, (x : V3) ∈ q ↔ (F x : P2) ∈ SquareRim) ∧
      ∃ (f : V3 → P2) (g : P2 → V3),
        FinitePiecewiseAffineOn f A ∧ FinitePiecewiseAffineOn g Square ∧
        InjOn f A ∧ InjOn g Square ∧
        LeftInvOn g f A ∧ LeftInvOn f g Square ∧
        f '' A = Square ∧ f '' q = SquareRim ∧
        (∀ x : A, (F x : P2) = f x) ∧
        ∃ (m : ℕ) (P : Polygon P2 (m + 3)),
          Function.Injective P ∧ P.HasSimplicialEdges ∧
          P.boundary ℝ = f '' R.boundary ℝ ∧
          (∀ x ∈ A, f x ∈ P.boundary ℝ ↔ x ∈ R.boundary ℝ) ∧
          P.boundary ℝ ⊆ interior Square ∧
          ∃ U : Set X, IsOpen U ∧ s.map '' R.boundary ℝ ⊆ U ∧
            S ∩ U = s.map '' (A \ q) ∧
            ∃ B : ↥(S ∩ U) ≃ₜ ↥(interior Square),
              ∀ x, (B x : P2) = f (s.parametrization.symm ⟨x, x.property.1⟩) := by
  classical
  obtain ⟨p, hp⟩ := hd.sdiff_nonempty
  obtain ⟨K, hK, hKs⟩ := exists_finite_unitCubeSphere (ι := Fin 3)
  have hsphere : Sphere = frontier (closedBall (0 : V3) 1) := by
    rw [frontier_closedBall _ one_ne_zero]
  have hRS : R.boundary ℝ ⊆ Sphere := hd.1.trans hdS
  obtain ⟨A, q, hA, hAS, hRA, hpA, hopen⟩ :=
    K.exists_convex_frontier_disk_of_compact_with_open_interior hK
      (isCompact_closedBall (0 : V3) 1) (convex_closedBall (0 : V3) 1)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩
      (hKs.trans hsphere) (F := P2) (by simp [Module.finrank_prod])
      ⟨p, hsphere.subset (hdS hp.1)⟩ R.isCompact_boundary (hRS.trans hsphere.subset) hp.2
  rw [← hsphere] at hAS hopen
  have hSquare := CoordinateHalfBoxes.base_ballPair (by norm_num : (0 : ℝ) < 1)
  obtain ⟨F, hF, hFq⟩ := hA.exists_homeomorph hSquare
  have hFinv := hF.symm
  obtain ⟨f, hf, hFf⟩ := hF
  obtain ⟨g, hg, hGg⟩ := hFinv
  have hgf : LeftInvOn g f A := by
    intro x hx
    rw [← hFf ⟨x, hx⟩, ← hGg, F.symm_apply_apply]
  have hfg : LeftInvOn f g Square := by
    intro x hx
    rw [← hGg ⟨x, hx⟩, ← hFf, F.apply_symm_apply]
  have hfi : InjOn f A := hgf.injOn
  have hgi : InjOn g Square := hfg.injOn
  have hfA : f '' A = Square := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hFf ⟨x, hx⟩]
      exact (F ⟨x, hx⟩).property
    · intro hy
      exact ⟨F.symm ⟨y, hy⟩, (F.symm ⟨y, hy⟩).property,
        (hFf _).symm.trans (congrArg Subtype.val (F.apply_symm_apply _))⟩
  have hfq : f '' q = SquareRim := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hFf ⟨x, hA.1 hx⟩]
      exact (hFq _).mp hx
    · intro hy
      let x := F.symm ⟨y, hSquare.1 hy⟩
      have hxq : (x : V3) ∈ q := (hFq x).mpr (by simpa [x] using hy)
      exact ⟨x, hxq, (hFf x).symm.trans (congrArg Subtype.val (F.apply_symm_apply _))⟩
  have hRAsub : R.boundary ℝ ⊆ A := hRA.trans sdiff_subset
  obtain ⟨m, P, hPi, hP, hPb⟩ :=
    R.exists_polygon_finitePL_image hR hRi hf hRAsub (hfi.mono hRAsub)
  have hPmem (x : V3) (hx : x ∈ A) : f x ∈ P.boundary ℝ ↔ x ∈ R.boundary ℝ := by
    rw [hPb]
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact hfi (hRAsub hy) hx hyx ▸ hy
    · exact fun hy => mem_image_of_mem f hy
  have hSquareInt : interior Square = Square \ SquareRim :=
    hSquare.interior_eq_sdiff_of_finrank_eq rfl
  have hFint (x : A) : (x : V3) ∈ A \ q ↔ (F x : P2) ∈ interior Square := by
    rw [hSquareInt]
    simp only [mem_sdiff, x.property, (F x).property, true_and]
    exact not_congr (hFq x)
  have hPint : P.boundary ℝ ⊆ interior Square := by
    rw [hPb]
    rintro _ ⟨x, hx, rfl⟩
    rw [← hFf ⟨x, hRAsub hx⟩]
    exact (hFint _).mp (hRA hx)
  let V : Set Sphere := (Subtype.val : Sphere → V3) ⁻¹' (A \ q)
  have hVS : IsOpen (s.parametrization '' V) := s.parametrization.isOpenMap _ hopen
  obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.mp hVS
  have hUmap (x : Sphere) : (s.parametrization x : X) ∈ U ↔ (x : V3) ∈ A \ q := by
    change s.parametrization x ∈ (Subtype.val : S → X) ⁻¹' U ↔ _
    rw [hUeq]
    exact s.parametrization.injective.mem_set_image
  have hrU : s.map '' R.boundary ℝ ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    rw [s.map_eq ⟨x, hRS hx⟩]
    exact (hUmap _).mpr (hRA hx)
  have hSU : S ∩ U = s.map '' (A \ q) := by
    ext y
    constructor
    · rintro ⟨hyS, hyU⟩
      obtain ⟨x, hx⟩ := s.parametrization.surjective ⟨y, hyS⟩
      refine ⟨x, (hUmap x).mp ?_, (s.map_eq x).trans (congrArg Subtype.val hx)⟩
      simpa only [hx] using hyU
    · rintro ⟨x, hx, rfl⟩
      rw [s.map_eq ⟨x, hAS hx.1⟩]
      exact ⟨(s.parametrization ⟨x, hAS hx.1⟩).property, (hUmap _).mpr hx⟩
  have hphysical (x : Sphere) : (x : V3) ∈ A \ q ↔ (s.parametrization x : X) ∈ S ∩ U := by
    simp only [mem_inter_iff, (s.parametrization x).property, true_and]
    exact (hUmap x).symm
  let physical := s.parametrization.restrictSubsets (sdiff_subset.trans hAS)
    inter_subset_left hphysical
  let planar := F.restrictSubsets sdiff_subset interior_subset hFint
  let B := physical.symm.trans planar
  refine ⟨p, A, q, F, hp, hpA, hA, hAS, hRA, hopen, ⟨f, hf, hFf⟩, hFq,
    f, g, hf, hg, hfi, hgi, hgf, hfg, hfA, hfq, hFf,
    m, P, hPi, hP, hPb, hPmem, hPint, U, hU, hrU, hSU, B, ?_⟩
  intro x
  exact hFf _

end PoincareConjecture.M76
