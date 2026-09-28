import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusSliceAcceleration
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ConformalMinimumHarmonic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

open Proofs.M09 CoordinateExponential ConnectionVariation

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

theorem m64Annulus_intrinsic_tension_eq_zero_of_conformal_minimum
    (D : LeviCivitaData g) (A : M64Annulus g c0 c1)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram g A.map p 0 0 = m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map m64AnnulusInterior)
    {x s : ℝ} (hp : annulusPoint x s ∈ m64AnnulusInterior) :
    rampHorizontalCovariantDerivative D (fun y => A.map (annulusPoint y s))
      (fun y => curveVelocity (fun z => A.map (annulusPoint z s)) y) x +
    rampHorizontalCovariantDerivative D (fun r => A.map (annulusPoint x r))
      (fun r => curveVelocity (fun z => A.map (annulusPoint x z)) r) s = 0 := by
  let p := annulusPoint x s
  let b := A.map p
  let c := extChartAt (𝓡 n) b
  let U := m64AnnulusInterior ∩ A.map ⁻¹' c.source
  let u := c ∘ A.map
  let B := g.pullbackCoefficients c.symm
  let e0 : LoopPlane := EuclideanSpace.single (0 : Fin 2) 1
  let e1 : LoopPlane := EuclideanSpace.single (1 : Fin 2) 1
  have hU : IsOpen U := hA.continuousOn.isOpen_inter_preimage
    isOpen_m64AnnulusInterior (isOpen_extChartAt_source b)
  have hpU : p ∈ U := ⟨hp, mem_extChartAt_source b⟩
  have hAU := hA.mono (show U ⊆ m64AnnulusInterior from inter_subset_left)
  have hchart : MapsTo A.map U c.source := fun _ hq => hq.2
  have hharm := m64Annulus_chart_harmonic_of_conformal_minimum
    A hminimum hconformal b hU inter_subset_left hAU hchart p hpU
  change (∑ i : Fin 2, covDerivAlong (christoffelBilinear B) u
    (fun q => fderiv ℝ u q (EuclideanSpace.basisFun (Fin 2) ℝ i))
      (EuclideanSpace.basisFun (Fin 2) ℝ i) p) = 0 at hharm
  simp only [Fin.sum_univ_two, EuclideanSpace.basisFun_apply] at hharm
  have hline0 : ContDiff ℝ ∞ (fun y => annulusPoint y s) := by
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · simpa [annulusPoint] using! (contDiff_id : ContDiff ℝ ∞ (id : ℝ → ℝ))
    · simpa [annulusPoint] using (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => s))
  have hline1 : ContDiff ℝ ∞ (annulusPoint x) := by
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · simpa [annulusPoint] using (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => x))
    · simpa [annulusPoint] using! (contDiff_id : ContDiff ℝ ∞ (id : ℝ → ℝ))
  let J0 := (fun y => annulusPoint y s) ⁻¹' U
  let J1 := (annulusPoint x) ⁻¹' U
  have hJ0 : IsOpen J0 := hU.preimage hline0.continuous
  have hJ1 : IsOpen J1 := hU.preimage hline1.continuous
  have hacc0 := m64Annulus_slice_acceleration_in_chart D b hU hAU hchart
    hJ0 hline0.contDiffOn (fun _ hq => hq) e0
    (fun y _ => m64AnnulusPoint_horizontal_hasDerivAt s y) hpU
  have hacc1 := m64Annulus_slice_acceleration_in_chart D b hU hAU hchart
    hJ1 hline1.contDiffOn (fun _ hq => hq) e1
    (fun r _ => m64AnnulusPoint_vertical_hasDerivAt x r) hpU
  have hsum := congrArg₂ (fun v w : TangentSpace (𝓡 n) (A.map p) => v + w) hacc0 hacc1
  apply hsum.trans
  have hz := congrArg (fun v : EuclideanSpace ℝ (Fin n) =>
    chartVectorField b v (A.map p)) hharm
  simpa only [chartVectorField, VectorField.mpullback, map_add, map_zero] using hz

end PoincareConjecture
