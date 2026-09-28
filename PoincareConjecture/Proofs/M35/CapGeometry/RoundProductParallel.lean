import PoincareConjecture.Proofs.M35.CapGeometry.RoundProductConnection
import PoincareConjecture.Proofs.M35.CapGeometry.RoundSurfaceParallel









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

local notation "V" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)



theorem product_parallel_horizontal_zero
    {g : RiemannianMetric 3 V} {h : RiemannianMetric 2 E2}
    (D : LeviCivitaData g) (Dh : LeviCivitaData h) {x : V}
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v : V,
      g.inner y u v = h.inner (cylinderCoordinateEquiv y).1
        (cylinderCoordinateEquiv u).1 (cylinderCoordinateEquiv v).1 +
        (cylinderCoordinateEquiv u).2 * (cylinderCoordinateEquiv v).2)
    {Z : V → V} (hZ : ContDiffAt ℝ ∞ Z x)
    (hparallel : ∀ᶠ y in 𝓝 x, ∀ v : V, D.connection Z y v = 0)
    (hpos : ∀ u v : E2,
      h.inner (cylinderCoordinateEquiv x).1 u u = 1 →
      h.inner (cylinderCoordinateEquiv x).1 v v = 1 →
      h.inner (cylinderCoordinateEquiv x).1 u v = 0 →
        0 < Dh.sectionalCurvature (cylinderCoordinateEquiv x).1 u v) :
    (cylinderCoordinateEquiv (Z x)).1 = 0 := by
  let L := (ContinuousLinearMap.fst ℝ E2 ℝ).comp
    cylinderCoordinateEquiv.toContinuousLinearMap
  let phi : E2 → V := fun y => cylinderCoordinateEquiv.symm
    (y, (cylinderCoordinateEquiv x).2)
  let Y : E2 → E2 := fun y => L (Z (phi y))
  have hphi : ContDiff ℝ ∞ phi :=
    cylinderCoordinateEquiv.symm.contDiff.comp (contDiff_id.prodMk contDiff_const)
  have hphi0 : phi (cylinderCoordinateEquiv x).1 = x :=
    cylinderCoordinateEquiv.symm_apply_apply x
  have hZphi : ContDiffAt ℝ ∞ Z (phi (cylinderCoordinateEquiv x).1) := by
    simpa only [hphi0] using hZ
  have hY : ContDiffAt ℝ ∞ Y (cylinderCoordinateEquiv x).1 :=
    L.contDiff.contDiffAt.comp _ (hZphi.comp _ hphi.contDiffAt)
  have hdiff : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ Z y :=
    ((hZ.of_le (by norm_cast : (1 : ℕ∞ω) ≤ ∞)).eventually (by simp)).mono
      fun _ hy => hy.differentiableAt (by simp)
  have ht : Tendsto phi (𝓝 (cylinderCoordinateEquiv x).1) (𝓝 x) := by
    have hc : ContinuousAt phi (cylinderCoordinateEquiv x).1 :=
      hphi.continuous.continuousAt
    simpa only [hphi0] using hc.tendsto
  have hYparallel : ∀ᶠ y in 𝓝 (cylinderCoordinateEquiv x).1,
      ∀ v : E2, Dh.connection Y y v = 0 := by
    filter_upwards [ht.eventually hmetric.eventually_nhds,
      ht.eventually hparallel, ht.eventually hdiff] with y hmy hpy hdy v
    have hc := product_connection_horizontal D Dh hmy hdy v
    have hz := hpy (cylinderCoordinateEquiv.symm (v, 0))
    have hcz := congrArg (fun a : V => (cylinderCoordinateEquiv a).1) hz
    have he := hc.trans hcz
    change @Eq E2 _ _ at he
    simp only [phi, ContinuousLinearEquiv.apply_symm_apply, map_zero, Prod.fst_zero] at he
    have hbase : (cylinderCoordinateEquiv (phi y)).1 = y := by
      dsimp only [phi]
      rw [ContinuousLinearEquiv.apply_symm_apply]
    change (Dh.connection Y (cylinderCoordinateEquiv (phi y)).1 v : E2) = 0 at he
    exact (congrArg (fun a : E2 => (Dh.connection Y a v : E2)) hbase).symm.trans he
  have hz := positive_surface_parallel_germ Dh hY hYparallel hpos
  change L (Z (phi (cylinderCoordinateEquiv x).1)) = 0 at hz
  rw [hphi0] at hz
  exact hz



theorem product_parallel_axial_constant
    {g : RiemannianMetric 3 V} {h : RiemannianMetric 2 E2}
    (D : LeviCivitaData g) (Dh : LeviCivitaData h) {Ω : Set V}
    (hΩ : IsOpen Ω) (hconnected : IsPreconnected Ω)
    (hmetric : ∀ x ∈ Ω, ∀ u v : V,
      g.inner x u v = h.inner (cylinderCoordinateEquiv x).1
        (cylinderCoordinateEquiv u).1 (cylinderCoordinateEquiv v).1 +
        (cylinderCoordinateEquiv u).2 * (cylinderCoordinateEquiv v).2)
    {Z : V → V} (hZ : ContDiffOn ℝ ∞ Z Ω)
    (hparallel : ∀ x ∈ Ω, ∀ v : V, D.connection Z x v = 0)
    {x y : V} (hx : x ∈ Ω) (hy : y ∈ Ω) :
    (cylinderCoordinateEquiv (Z x)).2 = (cylinderCoordinateEquiv (Z y)).2 := by
  let L := (ContinuousLinearMap.snd ℝ E2 ℝ).comp
    cylinderCoordinateEquiv.toContinuousLinearMap
  have hs z hz := (hZ z hz).contDiffAt (hΩ.mem_nhds hz)
  have hd z hz : DifferentiableAt ℝ Z z := (hs z hz).differentiableAt (by simp)
  have hf : DifferentiableOn ℝ (fun z => L (Z z)) Ω :=
    fun z hz => (L.differentiableAt.comp z (hd z hz)).differentiableWithinAt
  have hder : Ω.EqOn (fderiv ℝ (fun z => L (Z z))) 0 := by
    intro z hz
    apply ContinuousLinearMap.ext
    intro w
    have hm : ∀ᶠ q in 𝓝 z, ∀ u v : V,
        g.inner q u v = h.inner (cylinderCoordinateEquiv q).1
          (cylinderCoordinateEquiv u).1 (cylinderCoordinateEquiv v).1 +
          (cylinderCoordinateEquiv u).2 * (cylinderCoordinateEquiv v).2 :=
      Filter.mem_of_superset (hΩ.mem_nhds hz) fun q hq => hmetric q hq
    have he := product_connection_axial D Dh hm (hd z hz) w
    have hp := congrArg (fun a : V => (cylinderCoordinateEquiv a).2) (hparallel z hz w)
    change fderiv ℝ (fun y => (cylinderCoordinateEquiv (Z y)).2) z w = 0
    simpa only [map_zero, Prod.snd_zero] using he.trans hp
  exact hΩ.is_const_of_fderiv_eq_zero hconnected hf hder hx hy



theorem product_parallel_reflection_false
    {g : RiemannianMetric 3 V} {h : RiemannianMetric 2 E2}
    (D : LeviCivitaData g) (Dh : LeviCivitaData h) {Ω : Set V}
    (hΩ : IsOpen Ω) (hconnected : IsPreconnected Ω)
    (hmetric : ∀ x ∈ Ω, ∀ u v : V,
      g.inner x u v = h.inner (cylinderCoordinateEquiv x).1
        (cylinderCoordinateEquiv u).1 (cylinderCoordinateEquiv v).1 +
        (cylinderCoordinateEquiv u).2 * (cylinderCoordinateEquiv v).2)
    {Z : V → V} (hZ : ContDiffOn ℝ ∞ Z Ω)
    (hparallel : ∀ x ∈ Ω, ∀ v : V, D.connection Z x v = 0)
    {x y : V} (hx : x ∈ Ω) (hy : y ∈ Ω)
    (hunit : g.inner x (Z x) (Z x) = 1)
    (hpos : ∀ u v : E2,
      h.inner (cylinderCoordinateEquiv x).1 u u = 1 →
      h.inner (cylinderCoordinateEquiv x).1 v v = 1 →
      h.inner (cylinderCoordinateEquiv x).1 u v = 0 →
        0 < Dh.sectionalCurvature (cylinderCoordinateEquiv x).1 u v)
    (hodd : (cylinderCoordinateEquiv (Z y)).2 = -(cylinderCoordinateEquiv (Z x)).2) :
    False := by
  have hh := product_parallel_horizontal_zero D Dh
    (Filter.mem_of_superset (hΩ.mem_nhds hx) fun z hz => hmetric z hz)
    ((hZ x hx).contDiffAt (hΩ.mem_nhds hx))
    (Filter.mem_of_superset (hΩ.mem_nhds hx) fun z hz => hparallel z hz) hpos
  have hc := product_parallel_axial_constant D Dh hΩ hconnected hmetric hZ hparallel hx hy
  have hz : (cylinderCoordinateEquiv (Z x)).2 = 0 := by linarith only [hc, hodd]
  have he := hmetric x hx (Z x) (Z x)
  rw [hh, hz, map_zero, zero_mul, add_zero] at he
  exact zero_ne_one (he.symm.trans hunit)

end PoincareConjecture.M35
