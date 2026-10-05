import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Coordinates.RoundCylinderParametrizedJets
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Coordinates.SphereChartMetric
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Asymptotics.EndCylinderPullback
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.InitialEstimates.EndTranslation
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.CylinderCoefficients

/-!
# Centered sphere-chart maps into the original end

The fixed geometric map sending cylinder coordinates through the chosen
sphere chart into the supplied end is smooth above height zero. Its
pullback of the ambient cylinder coefficients is the evolving Euclidean
model used by the frozen jet error. This is Proposition 12.7, pp. 298-299
and cylinder-asymptotics-by-end-energy.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology InnerProductSpace

namespace PoincareMT.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)

/-- The supplied end coordinates through the literal chosen sphere chart
(Proposition 12.7, pp. 298-299). -/
noncomputable def endSphereCylinderMap {g : RiemannianMetric 3 StandardCapSpace}
    (e : StandardCylindricalEnd g) (q : UnitTwoSphere)
    (p : RoundCylinderCoordinates) : StandardCapSpace :=
  e.coordinate ((chartAt E₂ q).symm p.1, p.2)

/-- The evolving Euclidean model is the frozen cylinder inner product in
the chosen sphere chart (Proposition 12.7, pp. 298-299). -/
theorem evolvingRoundCylinderModelCoefficients_eq_standardCylinderInner
    (u : ℝ) (q : UnitTwoSphere) (p v w : RoundCylinderCoordinates) :
    evolvingRoundCylinderModelCoefficients u p v w =
      standardCylinderInner u ((chartAt E₂ q).symm p.1, p.2)
        (mfderiv (𝓡 2) (𝓡 2) (chartAt E₂ q).symm p.1 v.1, v.2)
        (mfderiv (𝓡 2) (𝓡 2) (chartAt E₂ q).symm p.1 w.1, w.2) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  simp only [evolvingRoundCylinderModelCoefficients_apply, standardCylinderInner]
  have h := inner_mfderiv_sphere_chart_symm (E := EuclideanSpace ℝ (Fin 3)) (n := 2)
    q p.1 v.1 w.1
  rw [h]
  ring

variable {g : RiemannianMetric 3 StandardCapSpace} (e : StandardCylindricalEnd g)

/-- The centered chart map is smooth at every positive height
(Proposition 12.7, pp. 298-299). -/
theorem endSphereCylinderMap_contMDiffAt (q : UnitTwoSphere)
    {p : RoundCylinderCoordinates} (hp : 0 < p.2) :
    ContMDiffAt 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) ∞
      (endSphereCylinderMap e q) p :=
  (end_coordinate_contMDiffAt e (z := ((chartAt E₂ q).symm p.1, p.2)) hp).comp p
    (cylinderChart_symm_smooth q p)

/-- The derivative of the centered chart map retains the sphere-chart
inverse in the angular factor (Proposition 12.7, pp. 298-299). -/
theorem endSphereCylinderMap_mfderiv (q : UnitTwoSphere)
    {p : RoundCylinderCoordinates} (hp : 0 < p.2)
    (v : RoundCylinderCoordinates) :
    mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) (endSphereCylinderMap e q) p v =
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e.coordinate
        ((chartAt E₂ q).symm p.1, p.2)
        (mfderiv (𝓡 2) (𝓡 2) (chartAt E₂ q).symm p.1 v.1, v.2) := by
  have hf := (end_coordinate_contMDiffAt e
      (z := ((chartAt E₂ q).symm p.1, p.2)) hp).mdifferentiableAt (by simp)
  let c := chartAt E₂ q
  have hc : MDifferentiableAt (𝓡 2) (𝓡 2) c.symm p.1 := by
    apply ((contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞) (x := q)).contMDiffAt
      ?_).mdifferentiableAt (by simp)
    exact c.open_target.mem_nhds (by rw [roundCylinder_sphereChart_target]; trivial)
  let L₁ := ContinuousLinearMap.fst ℝ E₂ ℝ
  let L₂ := ContinuousLinearMap.snd ℝ E₂ ℝ
  have h₁ := hc.comp p L₁.mdifferentiableAt
  have h₂ := L₂.mdifferentiableAt (x := p)
  have hh := mfderiv_comp p hf (h₁.prodMk h₂)
  have hL₁ : mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 2) Prod.fst p = L₁ :=
    L₁.mfderiv_eq
  have hL₂ : mfderiv 𝓘(ℝ, RoundCylinderCoordinates) 𝓘(ℝ, ℝ) L₂ p = L₂ :=
    L₂.mfderiv_eq
  rw [mfderiv_prodMk h₁ h₂, mfderiv_comp p hc L₁.mdifferentiableAt, hL₁, hL₂] at hh
  exact congrArg (fun L => L v) hh

/-- Above height two, the ambient cylinder coefficients pull back to the
evolving Euclidean model in the chosen chart (Proposition 12.7, pp. 298-299). -/
theorem endCylinderCoefficients_endSphereCylinderMap (s : ℝ) (q : UnitTwoSphere)
    {p : RoundCylinderCoordinates} (hp : 2 < p.2)
    (v w : RoundCylinderCoordinates) :
    endCylinderCoefficients e s (endSphereCylinderMap e q p)
      (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) (endSphereCylinderMap e q) p v)
      (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) (endSphereCylinderMap e q) p w) =
    evolvingRoundCylinderModelCoefficients s p v w := by
  have hp0 : 0 < p.2 := lt_trans (by norm_num : (0 : ℝ) < 2) hp
  rw [endSphereCylinderMap_mfderiv e q hp0 v, endSphereCylinderMap_mfderiv e q hp0 w]
  change endCylinderCoefficients e s
      (e.coordinate ((chartAt E₂ q).symm p.1, p.2))
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e.coordinate
        ((chartAt E₂ q).symm p.1, p.2)
        (mfderiv (𝓡 2) (𝓡 2) (chartAt E₂ q).symm p.1 v.1, v.2))
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e.coordinate
        ((chartAt E₂ q).symm p.1, p.2)
        (mfderiv (𝓡 2) (𝓡 2) (chartAt E₂ q).symm p.1 w.1, w.2)) = _
  rw [endCylinderCoefficients_coordinate e s hp]
  exact (evolvingRoundCylinderModelCoefficients_eq_standardCylinderInner
    s q p v w).symm

/-- Axial translation of the centered chart map is the same map at the
translated height (Proposition 12.7, pp. 298-299). -/
theorem endAxialTranslation_endSphereCylinderMap (j : ℕ) (q : UnitTwoSphere)
    {p : RoundCylinderCoordinates} (hp : 0 ≤ p.2) :
    endAxialTranslation e j (endSphereCylinderMap e q p) =
      e.coordinate ((chartAt E₂ q).symm p.1, p.2 + j) :=
  endAxialTranslation_coordinate e j (z := ((chartAt E₂ q).symm p.1, p.2)) hp

end PoincareMT.M34
