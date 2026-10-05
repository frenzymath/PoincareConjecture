import PoincareLib.Geometry.CurveShortening.Deformation.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Deformation.Plateau.InteriorRegularityConeVectorGreen
import PoincareLib.Geometry.CurveShortening.Deformation.Plateau.InteriorRegularityWeakGluing

/-!
# The actual cone is a genuine local weak replacement

The constructed circle's true AE trace identifies the two boundary
functionals. The proved cone Green formula therefore cancels the
original weak map's disk Green formula, constructing the genuine
target-valued competitor with its same explicit L2 fields. Morrey ICM
1950, printed pp. 183-185, for Morgan--Tian Lemma 19.2, pp. 437-438;
M65 derivation 38, actual weak gluing.
-/

set_option autoImplicit false

open Set Metric MeasureTheory
open scoped Topology ContDiff SchwartzMap

namespace PoincareMT.M65LocalWeakMap

open M65Interior

/-- At an actual Green radius, the genuine AC circle and target chart
give an actual cone competitor in the original local weak-map class.
No weak derivative or Green premise is imposed on the new cone.
Morrey ICM pp. 183-185; MT Lemma 19.2, pp. 437-438; derivation 38. -/
theorem exists_cone_replacement {M : Type*} {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {U : Set LoopPlane}
    (F : M65LocalWeakMap e U) (x : LoopPlane)
    {r ρ K : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hK : 0 ≤ K)
    (hDU : closedBall x r ⊆ U) (P : EuclideanSpace ℝ (Fin 3) → M)
    {v d : ℝ → EuclideanSpace ℝ (Fin 3)} {v0 : EuclideanSpace ℝ (Fin 3)}
    (hv : AbsolutelyContinuousOnInterval v (-Real.pi) Real.pi)
    (hper : v (-Real.pi) = v Real.pi)
    (hg : ContDiffOn ℝ 1 (e ∘ P) (ball 0 (2 * ρ)))
    (h0 : v0 ∈ closedBall 0 ρ)
    (hvb : MapsTo v (Icc (-Real.pi) Real.pi) (closedBall 0 ρ))
    (hd : MemLp d 2 (volume.restrict (Icc (-Real.pi) Real.pi)))
    (hinc : ∀ t ∈ Icc (-Real.pi) Real.pi, ∀ u ∈ Icc (-Real.pi) Real.pi,
      v u - v t = ∫ θ in t..u, d θ)
    (hD : ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) ρ, ‖fderiv ℝ (e ∘ P) y‖ ≤ K)
    (htrace : (fun θ => P (v θ)) =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)]
      fun θ => F.value (polarPlane x (r, θ)))
    (hgreen : ∀ (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2) (j : Fin N),
      (∫ z in closedBall x r, F.derivative i z j * test z +
        e (F.value z) j * fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
        r * ∫ θ in (-Real.pi)..Real.pi,
          e (F.value (polarPlane x (r, θ))) j * test (polarPlane x (r, θ)) *
            Proofs.M58.angularPoint θ i) :
    ∃ G : M65LocalWeakMap e U,
      (∀ z ∈ closedBall x r, G.value z = coneDiskMap P r v0 v x z ∧
        ∀ i, G.derivative i z = coneDiskField (e ∘ P) r v0 v d x i z) ∧
      ∀ z ∉ closedBall x r, G.value z = F.value z ∧
        ∀ i, G.derivative i z = F.derivative i z := by
  have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hvc : ContinuousOn v (Icc (-Real.pi) Real.pi) := by
    simpa only [uIcc_of_le hπ] using hv.continuousOn
  have hL := coneDisk_memLp hr hρ hK hvc hg h0 hvb hd hD x
  apply F.exists_disk_replacement x r hDU (coneDiskMap P r v0 v x)
    (coneDiskField (e ∘ P) r v0 v d x) hL.1 hL.2
  intro test i j
  let L : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ := EuclideanSpace.proj j
  calc
    _ = ∫ z in closedBall x r, L (coneDiskField (e ∘ P) r v0 v d x i z) * test z +
        L (coneDiskMap (e ∘ P) r v0 v x z) *
          fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
      apply setIntegral_congr_fun isClosed_closedBall.measurableSet
      intro z _
      change test z * _ + _ * e (coneDiskMap P r v0 v x z) j =
        coneDiskField (e ∘ P) r v0 v d x i z j * test z +
          e (coneDiskMap P r v0 v x z) j * _
      ring
    _ = r * ∫ θ in (-Real.pi)..Real.pi,
        e (P (v θ)) j * test (polarPlane x (r, θ)) * Proofs.M58.angularPoint θ i :=
      coneDisk_green_clm L hr hρ hK hv hper hg h0 hvb hd hinc hD x test (test.smooth 1) i
    _ = r * ∫ θ in (-Real.pi)..Real.pi,
        e (F.value (polarPlane x (r, θ))) j * test (polarPlane x (r, θ)) *
          Proofs.M58.angularPoint θ i := by
      congr 1
      apply intervalIntegral.integral_congr_ae_restrict
      rw [uIoc_of_le hπ]
      filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self htrace]
        with θ hθ
      rw [hθ]
    _ = ∫ z in closedBall x r, F.derivative i z j * test z +
        e (F.value z) j * fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i) :=
      (hgreen test i j).symm
    _ = _ := by
      apply setIntegral_congr_fun isClosed_closedBall.measurableSet
      intro z _
      ring

end PoincareMT.M65LocalWeakMap
