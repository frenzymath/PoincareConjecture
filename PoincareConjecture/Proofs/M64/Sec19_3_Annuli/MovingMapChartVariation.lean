import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingMapVariation
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.ChartEnergyFirstVariation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusChartEnergyVariation













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology BigOperators

universe u

namespace PoincareConjecture

open CoordinateExponential ConnectionVariation ConjugateVariation

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]





theorem m64AnnulusEnergyDensity_hasDerivAt_of_affine_chart
    (g : RiemannianMetric n M) (b : M) (v : ℝ × LoopPlane → M)
    (hv : ContMDiff 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v)
    (V : LoopPlane → EuclideanSpace ℝ (Fin n)) (hV : ContDiff ℝ ∞ V)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) {O : Set LoopPlane} (hO : IsOpen O)
    (hcoord : ∀ s ∈ Ioo (-epsilon) epsilon, ∀ p ∈ O,
      v (s, p) ∈ (extChartAt (𝓡 n) b).source ∧
        extChartAt (𝓡 n) b (v (s, p)) =
          extChartAt (𝓡 n) b (v (0, p)) + s • V p)
    (p : LoopPlane) (hp : p ∈ O) :
    let u := (extChartAt (𝓡 n) b) ∘ (fun p => v (0, p))
    let B := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
    HasDerivAt (fun s => m60EnergyDensity g (fun z => v (s, z)) p)
      (∑ i : Fin 2, B (u p)
        (covDerivAlong (christoffelBilinear B) u V (EuclideanSpace.basisFun (Fin 2) ℝ i) p)
        (fderiv ℝ u p (EuclideanSpace.basisFun (Fin 2) ℝ i))) 0 := by
  let c := extChartAt (𝓡 n) b
  let φ := fun p => v (0, p)
  let u := c ∘ φ
  let B := g.pullbackCoefficients c.symm
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  have hpchart : φ p ∈ c.source := (hcoord 0 hzero p hp).1
  have hslice (s : ℝ) : ContMDiff (𝓡 2) (𝓡 n) ∞ (fun p => v (s, p)) :=
    hv.comp ((contDiff_const.prodMk contDiff_id).contMDiff)
  have hu : ContDiffAt ℝ ∞ u p := contMDiffAt_iff_contDiffAt.mp
    ((contMDiffAt_extChartAt' (n := ∞)
      (by simpa only [c, extChartAt_source] using hpchart)).comp p (hslice 0 p))
  have hB : DifferentiableAt ℝ B (u p) :=
    ((g.contDiffOn_chartCoefficients b).contDiffAt
      ((isOpen_extChartAt_target b).mem_nhds (c.map_source hpchart))).differentiableAt
      (by simp)
  have hterm (i : Fin 2) := M60.hasDerivAt_affine_coordinate_energy (u := u) (V := V)
    p (e i) hB (isMetricCompatibleAt_chartCoefficients g b (c.map_source hpchart))
    (fun _ _ => g.symm _ _ _) (christoffelBilinear_chart_symm g b (u p))
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hterm i)
  apply hsum.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hzero] with s hs
  have heq : (fun z => c (v (s, z))) =ᶠ[𝓝 p] (fun z => u z + s • V z) := by
    filter_upwards [hO.mem_nhds hp] with z hz
    exact (hcoord s hs z hz).2
  have hd : HasFDerivAt (fun z => u z + s • V z)
      (fderiv ℝ u p + s • fderiv ℝ V p) p :=
    (hu.differentiableAt (by simp)).hasFDerivAt.add
      ((hV.differentiable (by simp) p).hasFDerivAt.const_smul s)
  rw [m60EnergyDensity_eq_chart g b
    ((hslice s).mdifferentiable (by simp) p) (hcoord s hs p hp).1]
  dsimp only [Function.comp_def]
  rw [heq.fderiv_eq, hd.fderiv, (hcoord s hs p hp).2, Finset.mul_sum]
  rfl






theorem m64AnnulusEnergy_hasDerivAt_of_affine_chart
    (g : RiemannianMetric n M) (b : M) (v : ℝ × LoopPlane → M)
    (hv : ContMDiff 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v)
    (V : LoopPlane → EuclideanSpace ℝ (Fin n)) (hV : ContDiff ℝ ∞ V)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) {O : Set LoopPlane} (hO : IsOpen O)
    (hdom : m64AnnulusDomain ⊆ O)
    (hcoord : ∀ s ∈ Ioo (-epsilon) epsilon, ∀ p ∈ O,
      v (s, p) ∈ (extChartAt (𝓡 n) b).source ∧
        extChartAt (𝓡 n) b (v (s, p)) =
          extChartAt (𝓡 n) b (v (0, p)) + s • V p) :
    let u := (extChartAt (𝓡 n) b) ∘ (fun p => v (0, p))
    let B := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
    let D := fun p => ∑ i : Fin 2, B (u p)
      (covDerivAlong (christoffelBilinear B) u V (EuclideanSpace.basisFun (Fin 2) ℝ i) p)
      (fderiv ℝ u p (EuclideanSpace.basisFun (Fin 2) ℝ i))
    IntegrableOn D m64AnnulusDomain volume ∧
      HasDerivAt (fun s => ∫ p in m64AnnulusDomain,
        m60EnergyDensity g (fun z => v (s, z)) p)
        (∫ p in m64AnnulusDomain, D p) 0 := by
  let u := (extChartAt (𝓡 n) b) ∘ (fun p => v (0, p))
  let B := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
  let D := fun p => ∑ i : Fin 2, B (u p)
    (covDerivAlong (christoffelBilinear B) u V (EuclideanSpace.basisFun (Fin 2) ℝ i) p)
    (fderiv ℝ u p (EuclideanSpace.basisFun (Fin 2) ℝ i))
  let E := fun q : ℝ × LoopPlane => m60EnergyDensity g (fun z => v (q.1, z)) q.2
  have hE : ContDiff ℝ ∞ E := contDiff_iff_contDiffAt.mpr fun q =>
    m60EnergyDensity_family_contDiffAt g (hv q)
  have hae : (fun p => fderiv ℝ E (0, p) (1, 0)) =ᵐ[volume.restrict m64AnnulusDomain] D := by
    filter_upwards [ae_restrict_mem m64AnnulusDomain_measurableSet] with p hp
    have hd : HasDerivAt (fun s => E (s, p)) (fderiv ℝ E (0, p) (1, 0)) 0 :=
      (hE.differentiable (by simp) (0, p)).hasFDerivAt.comp_hasDerivAt
        (l := E) (f := fun s : ℝ => (s, p)) (0 : ℝ)
        ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) p))
    exact hd.unique (m64AnnulusEnergyDensity_hasDerivAt_of_affine_chart
      g b v hv V hV hepsilon hO hcoord p (hdom hp))
  obtain ⟨hint, hd⟩ := m64AnnulusEnergy_hasDerivAt_of_smooth_variation g v hv 0
  refine ⟨hint.congr hae, ?_⟩
  have heq := integral_congr_ae hae
  change HasDerivAt (fun s => ∫ p in m64AnnulusDomain, E (s, p))
    (∫ p in m64AnnulusDomain, fderiv ℝ E (0, p) (1, 0)) 0 at hd
  rw [heq] at hd
  exact hd





theorem m64AnnulusEnergy_hasDerivAt_of_affine_chart_on
    (g : RiemannianMetric n M) (b : M) (f : LoopPlane → M)
    {O : Set LoopPlane} (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) ∞ f O)
    (hfO : MapsTo f O (extChartAt (𝓡 n) b).source)
    (V : LoopPlane → EuclideanSpace ℝ (Fin n)) (hV : ContDiff ℝ ∞ V)
    {v : ℝ × LoopPlane → M} {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v
      (Ioo (-epsilon) epsilon ×ˢ O))
    (hcoord : ∀ s ∈ Ioo (-epsilon) epsilon, ∀ p ∈ O,
      v (s, p) ∈ (extChartAt (𝓡 n) b).source ∧
        extChartAt (𝓡 n) b (v (s, p)) =
          extChartAt (𝓡 n) b (f p) + s • V p) :
    let u := (extChartAt (𝓡 n) b) ∘ f
    let B := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
    let D := fun p => ∑ i : Fin 2, B (u p)
      (covDerivAlong (christoffelBilinear B) u V (EuclideanSpace.basisFun (Fin 2) ℝ i) p)
      (fderiv ℝ u p (EuclideanSpace.basisFun (Fin 2) ℝ i))
    IntegrableOn D m64AnnulusDomain volume ∧
      HasDerivAt (fun s => ∫ p in m64AnnulusDomain,
        m60EnergyDensity g (fun z => v (s, z)) p)
        (∫ p in m64AnnulusDomain, D p) 0 := by
  let u := (extChartAt (𝓡 n) b) ∘ f
  let B := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
  let D := fun p => ∑ i : Fin 2, B (u p)
    (covDerivAlong (christoffelBilinear B) u V (EuclideanSpace.basisFun (Fin 2) ℝ i) p)
    (fderiv ℝ u p (EuclideanSpace.basisFun (Fin 2) ℝ i))
  let E := fun q : ℝ × LoopPlane => m60EnergyDensity g (fun z => v (q.1, z)) q.2
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  have hae : (fun p => fderiv ℝ E (0, p) (1, 0)) =ᵐ[volume.restrict m64AnnulusDomain] D := by
    filter_upwards [ae_restrict_mem m64AnnulusDomain_measurableSet] with p hp
    have hEp : ContDiffAt ℝ ∞ E (0, p) := m60EnergyDensity_family_contDiffAt g
      (hv.contMDiffAt ((isOpen_Ioo.prod hO).mem_nhds ⟨hzero, hdom hp⟩))
    have hd : HasDerivAt (fun s => E (s, p)) (fderiv ℝ E (0, p) (1, 0)) 0 :=
      (hEp.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
        (l := E) (f := fun s : ℝ => (s, p)) (0 : ℝ)
        ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) p))
    exact hd.unique (m64EnergyDensity_hasDerivAt_of_affine_chart
      g b f hO hf hfO V hV hepsilon hv hcoord p (hdom hp))
  obtain ⟨hint, hd⟩ :=
    m64AnnulusEnergy_hasDerivAt_of_local_smooth_variation g hepsilon hO hdom hv
  refine ⟨hint.congr hae, ?_⟩
  have heq := integral_congr_ae hae
  change HasDerivAt (fun s => ∫ p in m64AnnulusDomain, E (s, p))
    (∫ p in m64AnnulusDomain, fderiv ℝ E (0, p) (1, 0)) 0 at hd
  rw [heq] at hd
  exact hd

end PoincareConjecture
