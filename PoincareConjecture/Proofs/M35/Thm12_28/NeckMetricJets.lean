import PoincareConjecture.Proofs.M35.Thm12_28.CylinderFrechetJets
import PoincareConjecture.Proofs.M35.Thm12_28.NeckCurvature
import PoincareConjecture.Proofs.M35.Thm12_28.CylinderLeviCivita

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RoundCylinderClose

theorem euclidean_metric_error_component_abs_lt_shift
    {epsilon u : ℝ} {B : RoundCylinderTwoTensor}
    (h : RoundCylinderClose epsilon u B) (he : 0 < epsilon)
    (hlo : -1 ≤ u) (hu : u < 1) (q : UnitTwoSphere)
    (s : ℝ) (hs : s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (hk : 2 ≤ ⌊epsilon⁻¹⌋₊)
    (g : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)))
    (i j : Fin 3)
    (hg : (fun p : EuclideanSpace ℝ (Fin 3) => g.inner p
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)) =ᶠ[𝓝 0]
      (fun p => roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (M35.cylinderCoordinateEquiv p + (0, s)) i j))
    {r : ℕ} (hr : r ≤ 2) (a : Fin r → Fin 3) :
    |iteratedFDeriv ℝ r (fun p : EuclideanSpace ℝ (Fin 3) =>
      g.inner p (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j) -
        (M35.cylinderEuclideanMetric u hu).inner p
          (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j))
          0 (fun k => EuclideanSpace.basisFun (Fin 3) ℝ (a k))| < 52 * epsilon := by
  let f : RoundCylinderCoordinates → ℝ := fun p =>
    roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j -
      roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j
  have herror : (fun p : EuclideanSpace ℝ (Fin 3) => g.inner p
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j) -
        (M35.cylinderEuclideanMetric u hu).inner p
          (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)) =ᶠ[𝓝 0]
      (fun y => f (y + (0, s))) ∘ M35.cylinderCoordinateEquiv := by
    filter_upwards [hg] with p hp
    have hmodel : (M35.cylinderEuclideanMetric u hu).inner p
        (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j) =
        roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
          (M35.cylinderCoordinateEquiv p + (0, s)) i j := by
      rw [M35.cylinderEuclideanMetric_basis u hu q p i j,
        M35.roundCylinderGram_apply, M35.roundCylinderGram_apply]
      simp only [Prod.fst_add, add_zero]
    exact congrArg₂ (fun x y : ℝ => x - y) hp hmodel
  have hjet := (herror.filter_mono (nhdsWithin_le_nhds (s := univ))).iteratedFDerivWithin_eq
    (𝕜 := ℝ) herror.self_of_nhds r
  simp only [iteratedFDerivWithin_univ] at hjet
  have htransport := M35.iteratedFDeriv_cylinderCoordinateEquiv (fun y => f (y + (0, s))) 0 r
    (fun k => EuclideanSpace.basisFun (Fin 3) ℝ (a k))
  simp only [map_zero, M35.cylinderCoordinateEquiv_basis,
    iteratedFDeriv_comp_add_right, zero_add] at htransport
  have heq := (congrArg (fun A => A (fun k => EuclideanSpace.basisFun (Fin 3) ℝ (a k)))
    hjet).trans htransport
  exact (congrArg abs heq).trans_lt (h.iterated_error_component_abs_lt he hlo hu q s hs hk hr i j a)

theorem euclidean_metric_error_component_abs_lt
    {epsilon u : ℝ} {B : RoundCylinderTwoTensor}
    (h : RoundCylinderClose epsilon u B) (he : 0 < epsilon)
    (hlo : -1 ≤ u) (hu : u < 1) (q : UnitTwoSphere)
    (hk : 2 ≤ ⌊epsilon⁻¹⌋₊)
    (g : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)))
    (i j : Fin 3)
    (hg : (fun p : EuclideanSpace ℝ (Fin 3) => g.inner p
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)) =ᶠ[𝓝 0]
      (fun p => roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (M35.cylinderCoordinateEquiv p) i j))
    {r : ℕ} (hr : r ≤ 2) (a : Fin r → Fin 3) :
    |iteratedFDeriv ℝ r (fun p : EuclideanSpace ℝ (Fin 3) =>
      g.inner p (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j) -
        (M35.cylinderEuclideanMetric u hu).inner p
          (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j))
          0 (fun k => EuclideanSpace.basisFun (Fin 3) ℝ (a k))| < 52 * epsilon := by
  have hs : (0 : ℝ) ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr he), inv_pos.mpr he⟩
  apply h.euclidean_metric_error_component_abs_lt_shift he hlo hu q 0 hs hk g i j ?_ hr a
  simpa only [← Prod.zero_eq_mk, add_zero] using hg

end PoincareConjecture.RoundCylinderClose

namespace PoincareConjecture.StandardCylinderPatch

theorem euclidean_realization_coefficient_germ {length : ℝ} {center : StandardCapSpace}
    (N : StandardCylinderPatch length center) (g : RiemannianMetric 3 StandardCapSpace)
    (q : UnitTwoSphere) {p : EuclideanSpace ℝ (Fin 3)}
    (hp : (M35.cylinderCoordinateEquiv p).2 ∈ Ioo (-length) length)
    (g' : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)))
    (hg : ∀ᶠ y in 𝓝 p, g'.euclideanCoefficients y =
      g.pullbackCoefficients (N.coordinate ∘ M35.cylinderChart q) y)
    (i j : Fin 3) :
    (fun y : EuclideanSpace ℝ (Fin 3) => g'.inner y
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)) =ᶠ[𝓝 p]
      (fun y => roundCylinderTensorCoefficient (roundCylinderPullback g N.coordinate)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) (M35.cylinderCoordinateEquiv y) i j) := by
  have hU := (isOpen_Ioo.preimage
    (continuous_snd.comp M35.cylinderCoordinateEquiv.continuous)).mem_nhds hp
  filter_upwards [hg, hU] with y hy hdom
  have hval := congrArg (fun A : EuclideanSpace ℝ (Fin 3) →L[ℝ]
    EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ =>
      A (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)) hy
  exact hval.trans (N.euclideanChart_coefficient g q hdom i j)

end PoincareConjecture.StandardCylinderPatch
