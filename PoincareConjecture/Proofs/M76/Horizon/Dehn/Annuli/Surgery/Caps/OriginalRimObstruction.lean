import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Towers.MarkedRims
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallPairs
import Mathlib.Analysis.Convex.Contractible

set_option autoImplicit false
open Set Metric Geometry Topology
open scoped unitInterval

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "D2" => closedBall (0 : V2) 1

variable (L : Submodule ℤ V2) {α : Type*}
  {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3}
  {h : OpenPartialHomeomorph (V1 × V2) V3}
  (retained : HamiltonRetainedBlockChart (Fin 1) (Fin 2) L e h)
  {S : SimplicialComplex ℝ (V1 × V2)}
  {f : (V1 × V2) → chartShell L retained}
  {r : chartShell L retained → ℝ} {C : Set (chartShell L retained)}
  (s : Geometry.OriginalPLTower.Stage (fun _ : Unit ↦
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe
      (chartShell L retained) (chartShell_nonempty L retained)) S f r C)
  (hS : S.space = source)
  (hvalues : ∀ x ∈ sphere (0 : V1) 1 ×ˢ Q2, (f x : V3) = h (coordinates x))

include hvalues

theorem stage_rim_not_nullhomotopic (b : Bool) :
    ¬ (s.annulusRim hS b).Nullhomotopic := by
  intro hn
  have hn' := hn.comp_right ((chartShellRadial L retained).comp s.projection)
  have heq : ((chartShellRadial L retained).comp s.projection).comp
      (s.annulusRim hS b) = ContinuousMap.id Q2 :=
    ContinuousMap.ext (stage_radial_rim L retained s hS hvalues b)
  rw [heq] at hn'
  let : ContractibleSpace Q2 := (contractible_iff_id_nullhomotopic Q2).mpr hn'
  exact squareRimLoop_class_ne_one
    (Path.Homotopic.Quotient.eq.mpr (SimplyConnectedSpace.paths_homotopic _ _))

theorem stage_rim_not_factor_contractible (b : Bool)
    {X : Type*} [TopologicalSpace X] [ContractibleSpace X]
    (cap : C(X, s.Carrier)) (rim : C(Q2, X))
    (hwhole : ∀ u, cap (rim u) = s.annulusRim hS b u) : False := by
  have hn := ((id_nullhomotopic X).comp_left rim).comp_right cap
  have heq : cap.comp ((ContinuousMap.id X).comp rim) = s.annulusRim hS b :=
    ContinuousMap.ext hwhole
  rw [heq] at hn
  exact stage_rim_not_nullhomotopic L retained s hS hvalues b hn

theorem stage_rim_not_finitePL_cap (b : Bool)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D B : Set E} (hD : IsFinitePLBallPair (ℝ × ℝ) D B)
    (cap : C(D, s.Carrier)) (rim : C(Q2, D))
    (hwhole : ∀ u, cap (rim u) = s.annulusRim hS b u) : False := by
  obtain ⟨_, K, _, hcv, hne, H, _, _⟩ := hD
  let : ContractibleSpace K := hcv.contractibleSpace (hne.mono interior_subset)
  let : ContractibleSpace D := H.contractibleSpace
  exact stage_rim_not_factor_contractible L retained s hS hvalues b cap rim hwhole

theorem stage_rim_not_square_disk (b : Bool) (cap : C(D2, s.Carrier))
    (hwhole : ∀ u : Q2,
      cap ⟨u, sphere_subset_closedBall u.property⟩ = s.annulusRim hS b u) : False := by
  let : ContractibleSpace D2 := (convex_closedBall (0 : V2) 1).contractibleSpace
    ⟨0, mem_closedBall_self (by norm_num)⟩
  let rim : C(Q2, D2) := ⟨fun u ↦ ⟨u, sphere_subset_closedBall u.property⟩,
    continuous_subtype_val.subtype_mk _⟩
  exact stage_rim_not_factor_contractible L retained s hS hvalues b cap rim hwhole

theorem stage_rim_not_capped_cylinder (b : Bool)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D B : Set E} (hD : IsFinitePLBallPair (ℝ × ℝ) D B)
    (band : C(unitInterval × Q2, s.Carrier))
    (cap : C(D, s.Carrier)) (seam : C(Q2, D))
    (hzero : ∀ u, band (0, u) = s.annulusRim hS b u)
    (hone : ∀ u, band (1, u) = cap (seam u)) : False := by
  obtain ⟨_, K, _, hcv, hne, H, _, _⟩ := hD
  let : ContractibleSpace K := hcv.contractibleSpace (hne.mono interior_subset)
  let : ContractibleSpace D := H.contractibleSpace
  let hom : (s.annulusRim hS b).Homotopy (cap.comp seam) := {
    toContinuousMap := band
    map_zero_left := hzero
    map_one_left := hone }
  obtain ⟨x, hx⟩ := ((id_nullhomotopic D).comp_left seam).comp_right cap
  exact stage_rim_not_nullhomotopic L retained s hS hvalues b
    ⟨x, (show (s.annulusRim hS b).Homotopic (cap.comp seam) from ⟨hom⟩).trans hx⟩

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
