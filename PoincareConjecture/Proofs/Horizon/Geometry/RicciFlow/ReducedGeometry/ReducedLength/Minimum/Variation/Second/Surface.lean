import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Second.Density
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Second.Commutation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.MetricPair









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance secondVariationSurfaceDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance secondVariationSurfaceDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance secondVariationSurfaceBilinGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance secondVariationSurfaceBilinSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance secondVariationSurfaceEndGroup : NormedAddCommGroup (E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance secondVariationSurfaceEndSpace : NormedSpace ℝ (E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace
local instance secondVariationSurfaceConnectionGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance secondVariationSurfaceConnectionSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace

theorem curveCoordinateCovariantDerivative_congr (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (q : ℝ → E) {W Z : ℝ → E} {u : ℝ} (h : W =ᶠ[𝓝 u] Z) :
    curveCoordinateCovariantDerivative Γ q W u =
      curveCoordinateCovariantDerivative Γ q Z u := by
  simp only [curveCoordinateCovariantDerivative, h.deriv_eq, h.eq_of_nhds]

theorem curveCoordinateCovariantDerivative_sliceU
    (Γ : ℝ × E → E →L[ℝ] E →L[ℝ] E) (q W : ℝ × ℝ → E)
    {p : ℝ × ℝ} (hq : DifferentiableAt ℝ q p) (hW : DifferentiableAt ℝ W p) :
    curveCoordinateCovariantDerivative (fun x ↦ Γ (p.1, x))
        (fun u ↦ q (p.1, u)) (fun u ↦ W (p.1, u)) p.2 =
      coordinateCovariantU Γ q W p := by
  simp only [curveCoordinateCovariantDerivative,
    (coordinateSlice_snd_hasDerivAt q hq).deriv,
    (coordinateSlice_snd_hasDerivAt W hW).deriv, Prod.mk.eta,
    coordinateCovariantU, coordinatePartialU]

theorem curveCoordinateCovariantDerivative_sliceU_twice
    {Ω : Set (ℝ × ℝ)} {O : Set (ℝ × E)} (hΩ : IsOpen Ω)
    (Γ : ℝ × E → E →L[ℝ] E →L[ℝ] E) (q W : ℝ × ℝ → E)
    (hΓ : ContDiffOn ℝ ∞ Γ O) (hq : ContDiffOn ℝ ∞ q Ω)
    (hW : ContDiffOn ℝ ∞ W Ω) (hmap : MapsTo (fun p ↦ (p.1, q p)) Ω O)
    {p : ℝ × ℝ} (hp : p ∈ Ω) :
    curveCoordinateCovariantDerivative (fun x ↦ Γ (p.1, x)) (fun u ↦ q (p.1, u))
        (curveCoordinateCovariantDerivative (fun x ↦ Γ (p.1, x))
          (fun u ↦ q (p.1, u)) (fun u ↦ W (p.1, u))) p.2 =
      coordinateCovariantU Γ q (coordinateCovariantU Γ q W) p := by
  have heq : curveCoordinateCovariantDerivative (fun x ↦ Γ (p.1, x))
      (fun u ↦ q (p.1, u)) (fun u ↦ W (p.1, u)) =ᶠ[𝓝 p.2]
        (fun u ↦ coordinateCovariantU Γ q W (p.1, u)) := by
    have hnear := (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (hΩ.mem_nhds hp)
    filter_upwards [hnear] with u hu
    exact curveCoordinateCovariantDerivative_sliceU Γ q W
      (((hq (p.1, u) hu).contDiffAt (hΩ.mem_nhds hu)).differentiableAt (by simp))
      (((hW (p.1, u) hu).contDiffAt (hΩ.mem_nhds hu)).differentiableAt (by simp))
  rw [curveCoordinateCovariantDerivative_congr _ _ heq]
  exact curveCoordinateCovariantDerivative_sliceU Γ q _
    (((hq p hp).contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp))
    ((((coordinateCovariantU_contDiffOn hΩ Γ q W hΓ hq hW hmap) p hp).contDiffAt
      (hΩ.mem_nhds hp)).differentiableAt (by simp))

def coordinateCurvature (Γ : ℝ × E → E →L[ℝ] E →L[ℝ] E)
    (z : ℝ × E) (u v w : E) : E :=
  fderiv ℝ Γ z (0, u) v w - fderiv ℝ Γ z (0, v) u w +
    Γ z u (Γ z v w) - Γ z v (Γ z u w)

def surfaceActionDensity (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (P : ℝ × E → ℝ) (q : ℝ × ℝ → E) (p : ℝ × ℝ) : ℝ :=
  G (p.1, q p) (coordinatePartialS q p) (coordinatePartialS q p) / 2 + P (p.1, q p)

set_option maxHeartbeats 2200000 in
theorem surfaceActionDensity_second_hasDerivAt
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
    let DZ := coordinateCovariantS Γ q (coordinateCovariantU Γ q (coordinatePartialU q)) p
    let P₀ := fun x ↦ P (p.1, x)
    HasDerivAt (fun u ↦ deriv (fun v ↦ surfaceActionDensity G P q (p.1, v)) u)
      (G z DZ A + G z (coordinateCurvature Γ z Y A Y) A -
        G z (fderiv ℝ Γ z (1, 0) Y Y) A + G z DY DY +
        (fderiv ℝ (fderiv ℝ P₀) (q p) Y Y - fderiv ℝ P₀ (q p) (Γ z Y Y)) +
        fderiv ℝ P₀ (q p) Z) p.2 := by
  let I := (fun u : ℝ ↦ (p.1, u)) ⁻¹' Ω
  let U := (fun x : E ↦ (p.1, x)) ⁻¹' O
  let A := coordinatePartialS q
  let Y := coordinatePartialU q
  have hI : IsOpen I := hΩ.preimage (continuous_const.prodMk continuous_id)
  have hU : IsOpen U := hO.preimage (continuous_const.prodMk continuous_id)
  have hpI : p.2 ∈ I := by simpa only [I, mem_preimage, Prod.mk.eta] using hp
  have hA : ContDiffOn ℝ ∞ A Ω := coordinatePartialS_contDiffOn hΩ q hq
  have hY : ContDiffOn ℝ ∞ Y Ω := coordinatePartialU_contDiffOn hΩ q hq
  have hslice : MapsTo (fun u : ℝ ↦ (p.1, u)) I Ω := fun _ h ↦ h
  have htarget : MapsTo (fun x : E ↦ (p.1, x)) U O := fun _ h ↦ h
  have hqs : ContDiffOn ℝ ∞ (fun u ↦ q (p.1, u)) I :=
    hq.comp (contDiffOn_const.prodMk contDiffOn_id) hslice
  have hAs : ContDiffOn ℝ ∞ (fun u ↦ A (p.1, u)) I :=
    hA.comp (contDiffOn_const.prodMk contDiffOn_id) hslice
  have hqsmap : MapsTo (fun u ↦ q (p.1, u)) I U := fun u hu ↦ hmap hu
  have hfixed := chart_density_second_covariant_hasDerivAt hI hU
    (fun x ↦ G (p.1, x)) (fun x ↦ P (p.1, x)) (fun x ↦ Γ (p.1, x))
    (fun u ↦ q (p.1, u)) (fun u ↦ A (p.1, u))
    (hG.comp (contDiffOn_const.prodMk contDiffOn_id) htarget)
    (hP.comp (contDiffOn_const.prodMk contDiffOn_id) htarget)
    (hΓ.comp (contDiffOn_const.prodMk contDiffOn_id) htarget) hqs hAs hqsmap
    (fun x hx ↦ hsym (p.1, x) hx) (fun x hx ↦ hcompat (p.1, x) hx) hpI
  have hqp := ((hq p hp).contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp)
  have hAp := ((hA p hp).contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp)
  have hYp := ((hY p hp).contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp)
  have hfirst := curveCoordinateCovariantDerivative_sliceU Γ q A hqp hAp
  have hsecond := curveCoordinateCovariantDerivative_sliceU_twice hΩ Γ q A hΓ hq hA hmap hp
  have hy : deriv (fun u ↦ q (p.1, u)) =ᶠ[𝓝 p.2] (fun u ↦ Y (p.1, u)) := by
    have hnear := (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (hΩ.mem_nhds hp)
    filter_upwards [hnear] with u hu
    exact (coordinateSlice_snd_hasDerivAt q
      (((hq (p.1, u) hu).contDiffAt (hΩ.mem_nhds hu)).differentiableAt (by simp))).deriv
  have hZ := (curveCoordinateCovariantDerivative_congr (fun x ↦ Γ (p.1, x))
    (fun u ↦ q (p.1, u)) hy).trans (curveCoordinateCovariantDerivative_sliceU Γ q Y hqp hYp)
  rw [hfirst, hsecond, hZ, hy.eq_of_nhds] at hfixed
  have htorp := coordinateCovariant_torsion Γ q ((hq p hp).contDiffAt (hΩ.mem_nhds hp))
    (htor _ (hmap hp))
  have hcomm := coordinateCovariant_velocity_second hΩ Γ q hq
    (fun r hr ↦ htor _ (hmap hr)) hp
    (((hΓ _ (hmap hp)).contDiffAt (hO.mem_nhds (hmap hp))).differentiableAt (by simp))
  dsimp only [A] at hfixed
  rw [htorp, hcomm] at hfixed
  convert hfixed using 1 <;> try rfl
  simp only [map_add, map_sub, add_apply, sub_apply, coordinateCurvature, Prod.mk.eta]
  ring

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry
