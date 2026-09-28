import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.TargetChartEstimate
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.ConformalLogLaplacian










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff BigOperators

universe u

namespace PoincareConjecture

open CoordinateExponential ConnectionVariation

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




def M60SphereChartHarmonic (g : RiemannianMetric n M) (f : UnitTwoSphere → M) : Prop :=
  ∀ (b : M) (z : LoopPlane), f (m60SphereParameter z) ∈ (extChartAt (𝓡 n) b).source →
    let u := (extChartAt (𝓡 n) b) ∘ (f ∘ m60SphereParameter)
    let B := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
    covDerivAlong (christoffelBilinear B) u
        (fun r => fderiv ℝ u r (EuclideanSpace.basisFun (Fin 2) ℝ 0))
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) z +
      covDerivAlong (christoffelBilinear B) u
        (fun r => fderiv ℝ u r (EuclideanSpace.basisFun (Fin 2) ℝ 1))
        (EuclideanSpace.basisFun (Fin 2) ℝ 1) z = 0

variable {N : Type u} [TopologicalSpace N] [T2Space N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
  {g : RiemannianMetric 3 N}




theorem m60SphereAreaDensity_curvature_inequality (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (f : UnitTwoSphere → N)
    (hf : ContMDiff (𝓡 2) (𝓡 3) ∞ f) (hc : M60WeaklyConformal g f)
    (hharm : M60SphereChartHarmonic g f) (z : LoopPlane)
    (hz : 0 < m60SphereAreaDensity g f z) :
    let a := m60SphereAreaDensity g f
    let e := EuclideanSpace.basisFun (Fin 2) ℝ
    ((fderiv ℝ a z (e 0)) ^ 2 + (fderiv ℝ a z (e 1)) ^ 2) / a z -
      2 * a z * (16 / (‖z‖ ^ 2 + 4) ^ 2) *
        m60SphereCurvatureContribution D f (m60SphereParameter z) ≤
      fderiv ℝ (fun q => fderiv ℝ a q (e 0)) z (e 0) +
        fderiv ℝ (fun q => fderiv ℝ a q (e 1)) z (e 1) := by
  let φ := f ∘ m60SphereParameter
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let O := φ ⁻¹' (extChartAt (𝓡 3) (φ z)).source
  have hφ : ContMDiff (𝓡 2) (𝓡 3) ∞ φ := hf.comp m60SphereParameter_contMDiff
  have hO : IsOpen O := hφ.continuous.isOpen_preimage _ (isOpen_extChartAt_source _)
  have hzO : z ∈ O := mem_extChartAt_source _
  have hg (q : LoopPlane) (i j : Fin 2) :
      g.inner (φ q) (mfderiv (𝓡 2) (𝓡 3) φ q (e i)) (mfderiv (𝓡 2) (𝓡 3) φ q (e j)) =
        if i = j then m60SphereAreaDensity g f q else 0 := by
    have h := congrArg (fun G : Matrix (Fin 2) (Fin 2) ℝ => G i j)
      (m60AreaGram_eq_diagonal_of_weaklyConformal g f (hf.of_le (by simp)) hc q)
    exact h
  have hgeom := m60ConformalHarmonicChart_estimate D (φ z) hO hzO (e 0) (e 1)
    hφ.contMDiffOn (fun _ hq => hq) (fun q hq => hharm (φ z) q hq)
    (fun q _ => by simpa only [ite_true] using hg q 0 0)
    (fun q _ => by simpa only [ite_true] using hg q 1 1)
    (fun q _ => by simpa using hg q 0 1) hz
  have hR := m60SphereCurvatureContribution_plane D hD f (hf.of_le (by simp)) hc z hz
  dsimp only at hR
  have hR' := (div_eq_iff hz.ne').mp hR
  change D.curvatureTensor (φ z) (mfderiv (𝓡 2) (𝓡 3) φ z (e 0))
    (mfderiv (𝓡 2) (𝓡 3) φ z (e 1)) (mfderiv (𝓡 2) (𝓡 3) φ z (e 0))
    (mfderiv (𝓡 2) (𝓡 3) φ z (e 1)) = _ at hR'
  rw [hR'] at hgeom
  dsimp only
  convert! hgeom using 1
  ring



theorem m60Sphere_logAreaDensity_curvature_inequality (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (f : UnitTwoSphere → N)
    (hf : ContMDiff (𝓡 2) (𝓡 3) ∞ f) (hc : M60WeaklyConformal g f)
    (hharm : M60SphereChartHarmonic g f) (z : LoopPlane)
    (hz : 0 < m60SphereAreaDensity g f z) :
    -2 * (16 / (‖z‖ ^ 2 + 4) ^ 2) * m60SphereCurvatureContribution D f (m60SphereParameter z) ≤
      ∑ i : Fin 2, fderiv ℝ (fun y => fderiv ℝ
        (fun x => Real.log (m60SphereAreaDensity g f x)) y
          (EuclideanSpace.basisFun (Fin 2) ℝ i)) z
            (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
  let a := m60SphereAreaDensity g f
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let S := (fderiv ℝ a z (e 0)) ^ 2 + (fderiv ℝ a z (e 1)) ^ 2
  let L := fderiv ℝ (fun q => fderiv ℝ a q (e 0)) z (e 0) +
    fderiv ℝ (fun q => fderiv ℝ a q (e 1)) z (e 1)
  have ha : ContDiffAt ℝ 2 a z :=
    (m60SphereAreaDensity_contDiff g f hf hc).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  have heq : (∑ i : Fin 2, fderiv ℝ (fun y => fderiv ℝ (fun x => Real.log (a x)) y
      (e i)) z (e i)) = L / a z - S / (a z) ^ 2 := by
    rw [Fin.sum_univ_two, M60.second_fderiv_log ha hz.ne', M60.second_fderiv_log ha hz.ne']
    dsimp only [L, S]
    ring
  change _ ≤ ∑ i : Fin 2, fderiv ℝ (fun y => fderiv ℝ (fun x => Real.log (a x)) y
    (e i)) z (e i)
  rw [heq]
  have hgeom := m60SphereAreaDensity_curvature_inequality D hD f hf hc hharm z hz
  change S / a z - 2 * a z * (16 / (‖z‖ ^ 2 + 4) ^ 2) *
    m60SphereCurvatureContribution D f (m60SphereParameter z) ≤ L at hgeom
  calc
    _ = (S / a z - 2 * a z * (16 / (‖z‖ ^ 2 + 4) ^ 2) *
        m60SphereCurvatureContribution D f (m60SphereParameter z)) / a z - S / (a z) ^ 2 := by
      have hne : a z ≠ 0 := hz.ne'
      field_simp
      ring
    _ ≤ _ := sub_le_sub_right (div_le_div_of_nonneg_right hgeom hz.le) _

end PoincareConjecture
