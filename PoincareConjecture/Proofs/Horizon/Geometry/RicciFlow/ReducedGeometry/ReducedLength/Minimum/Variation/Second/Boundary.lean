import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Second.Surface

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

open ReducedLengthMinimum.Variational

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance secondVariationBoundaryDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance secondVariationBoundaryDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance secondVariationBoundaryBilinGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance secondVariationBoundaryBilinSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance secondVariationBoundaryEndGroup : NormedAddCommGroup (E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance secondVariationBoundaryEndSpace : NormedSpace ℝ (E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace
local instance secondVariationBoundaryConnectionGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance secondVariationBoundaryConnectionSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace

def surfaceAccelerationBoundaryPair (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (Γ : ℝ × E → E →L[ℝ] E →L[ℝ] E) (q : ℝ × ℝ → E) (p : ℝ × ℝ) : ℝ :=
  G (p.1, q p) (coordinatePartialS q p)
    (coordinateCovariantU Γ q (coordinatePartialU q) p)

set_option maxHeartbeats 1400000 in
theorem surfaceAccelerationBoundaryPair_hasDerivAt
    {Ω : Set (ℝ × ℝ)} {O : Set (ℝ × E)} (hΩ : IsOpen Ω) (hO : IsOpen O)
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (Γ : ℝ × E → E →L[ℝ] E →L[ℝ] E) (q : ℝ × ℝ → E)
    (hG : ContDiffOn ℝ ∞ G O) (hΓ : ContDiffOn ℝ ∞ Γ O)
    (hq : ContDiffOn ℝ ∞ q Ω) (hmap : MapsTo (fun p ↦ (p.1, q p)) Ω O)
    (hcompat : ∀ z ∈ O, ∀ y v w : E,
      fderiv ℝ (fun x ↦ G (z.1, x)) z.2 y v w =
        G z (Γ z y v) w + G z v (Γ z y w))
    {p : ℝ × ℝ} (hp : p ∈ Ω) :
    let z := (p.1, q p)
    let A := coordinatePartialS q p
    let Z := coordinateCovariantU Γ q (coordinatePartialU q) p
    HasDerivAt (fun r ↦ surfaceAccelerationBoundaryPair G Γ q (r, p.2))
      (G z (coordinateCovariantS Γ q (coordinatePartialS q) p) Z +
        G z A (coordinateCovariantS Γ q (coordinateCovariantU Γ q (coordinatePartialU q)) p) +
        fderiv ℝ G z (1, 0) A Z) p.1 := by
  let A := coordinatePartialS q
  let Y := coordinatePartialU q
  let Z := coordinateCovariantU Γ q Y
  have hA : ContDiffOn ℝ ∞ A Ω := coordinatePartialS_contDiffOn hΩ q hq
  have hY : ContDiffOn ℝ ∞ Y Ω := coordinatePartialU_contDiffOn hΩ q hq
  have hZ : ContDiffOn ℝ ∞ Z Ω := coordinateCovariantU_contDiffOn hΩ Γ q Y hΓ hq hY hmap
  have hqd := ((hq p hp).contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp)
  have hAd := ((hA p hp).contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp)
  have hZd := ((hZ p hp).contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp)
  have hGd := ((hG _ (hmap hp)).contDiffAt (hO.mem_nhds (hmap hp))).differentiableAt (by simp)
  have hgraph : HasDerivAt (fun r : ℝ ↦ (r, q (r, p.2))) (1, A p) p.1 :=
    (hasDerivAt_id p.1).prodMk (coordinateSlice_fst_hasDerivAt q hqd)
  have hGc : HasDerivAt (fun r : ℝ ↦ G (r, q (r, p.2)))
      (fderiv ℝ G (p.1, q p) (1, A p)) p.1 := hGd.hasFDerivAt.comp_hasDerivAt p.1 hgraph
  have hsp := (hasFDerivAt_spatial hO G hG (hmap hp)).fderiv
  have hc := hcompat (p.1, q p) (hmap hp) (A p) (A p) (Z p)
  rw [hsp] at hc
  change fderiv ℝ G (p.1, q p) (0, A p) (A p) (Z p) = _ at hc
  have hcompat' : fderiv ℝ G (p.1, q p) (1, A p) (A p) (Z p) =
      G (p.1, q p) (Γ (p.1, q p) (A p) (A p)) (Z p) +
        G (p.1, q p) (A p) (Γ (p.1, q p) (A p) (Z p)) +
        fderiv ℝ G (p.1, q p) (1, 0) (A p) (Z p) := by
    rw [show ((1 : ℝ), A p) = (1, (0 : E)) + (0, A p) by simp,
      map_add, add_apply, add_apply, hc]
    ring
  have h := chart_pair_moving_covariant_hasDerivAt
    (fun r ↦ G (r, q (r, p.2))) (Γ (p.1, q p))
    (fderiv ℝ G (p.1, q p) (1, 0)) (fderiv ℝ G (p.1, q p) (1, A p))
    hGc (coordinateSlice_fst_hasDerivAt A hAd) (coordinateSlice_fst_hasDerivAt Z hZd) hcompat'
  exact h

set_option maxHeartbeats 1600000 in
theorem surfaceActionDensity_second_boundary
    {Ω : Set (ℝ × ℝ)} {O : Set (ℝ × E)} (hΩ : IsOpen Ω) (hO : IsOpen O)
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (P : ℝ × E → ℝ)
    (Γ : ℝ × E → E →L[ℝ] E →L[ℝ] E) (q : ℝ × ℝ → E)
    (hG : ContDiffOn ℝ ∞ G O) (hP : ContDiffOn ℝ ∞ P O)
    (hΓ : ContDiffOn ℝ ∞ Γ O) (hq : ContDiffOn ℝ ∞ q Ω)
    (hmap : MapsTo (fun p ↦ (p.1, q p)) Ω O)
    (hsym : ∀ z ∈ O, ∀ v w : E, G z v w = G z w v)
    (hcompat : ∀ z ∈ O, ∀ y v w : E,
      fderiv ℝ (fun x ↦ G (z.1, x)) z.2 y v w =
        G z (Γ z y v) w + G z v (Γ z y w))
    (htor : ∀ z ∈ O, ∀ v w : E, Γ z v w = Γ z w v)
    {p : ℝ × ℝ} (hp : p ∈ Ω) :
    let z := (p.1, q p)
    let A := coordinatePartialS q p
    let Y := coordinatePartialU q p
    let Z := coordinateCovariantU Γ q (coordinatePartialU q) p
    let DY := coordinateCovariantS Γ q (coordinatePartialU q) p
    let DA := coordinateCovariantS Γ q (coordinatePartialS q) p
    let P₀ := fun x ↦ P (p.1, x)
    deriv (fun u ↦ deriv (fun v ↦ surfaceActionDensity G P q (p.1, v)) u) p.2 =
      deriv (fun r ↦ surfaceAccelerationBoundaryPair G Γ q (r, p.2)) p.1 +
      (G z DY DY + G z (coordinateCurvature Γ z Y A Y) A -
        G z (fderiv ℝ Γ z (1, 0) Y Y) A +
        (fderiv ℝ (fderiv ℝ P₀) (q p) Y Y - fderiv ℝ P₀ (q p) (Γ z Y Y))) -
      (G z DA Z - fderiv ℝ P₀ (q p) Z + fderiv ℝ G z (1, 0) A Z) := by
  have hd := (surfaceActionDensity_second_hasDerivAt hΩ hO G P Γ q
    hG hP hΓ hq hmap hsym hcompat htor hp).deriv
  have hb := (surfaceAccelerationBoundaryPair_hasDerivAt hΩ hO G Γ q hG hΓ hq hmap hcompat hp).deriv
  dsimp only at hd hb ⊢
  rw [hd, hb, hsym _ (hmap hp)
    (coordinateCovariantS Γ q (coordinateCovariantU Γ q (coordinatePartialU q)) p)
    (coordinatePartialS q p)]
  ring

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry
