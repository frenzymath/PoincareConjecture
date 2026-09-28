import PoincareConjecture.Proofs.M35.CapGeometry.ReflectedChartField

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set VectorField
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35

local notation "V" => EuclideanSpace ℝ (Fin 3)
local notation "Ip" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace V M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}

theorem twistedChartLift_mpullback_comp
    (N : M27TwistedSphereLineFlowCertificate K) (q : UnitTwoSphere)
    (F : M → V) (Z : V → V) (p : V)
    (hF : MDifferentiableAt (𝓡 3) (𝓡 3) F (N.cover (cylinderChart q p))) :
    twistedChartLift N q (mpullback (𝓡 3) (𝓡 3) F Z) p =
      pullback ℝ (F ∘ (N.cover ∘ cylinderChart q)) Z p := by
  have hcoord : (mfderivWithin (𝓡 3) (𝓡 3) (N.cover ∘ cylinderChart q) univ p).IsInvertible := by
    simpa only [mfderivWithin_univ] using twistedProductChart_invertible N q p
  have hfirst := mpullbackWithin_comp_of_right
    (I := 𝓡 3) (I' := 𝓡 3) (I'' := 𝓡 3)
    (f := N.cover ∘ cylinderChart q) (g := F) («V» := Z)
    (s := univ) (t := univ) (x₀ := p) hF.mdifferentiableWithinAt
    (fun _ _ => mem_univ _) (uniqueMDiffWithinAt_univ (𝓡 3)) hcoord
  have hcyl : (mfderivWithin (𝓡 3) Ip (cylinderChart q) univ p).IsInvertible := by
    simpa only [mfderivWithin_univ] using cylinderChart_mfderiv_invertible q p
  have hsecond := mpullbackWithin_comp_of_right
    (I := 𝓡 3) (I' := Ip) (I'' := 𝓡 3)
    (f := cylinderChart q) (g := N.cover) («V» := mpullback (𝓡 3) (𝓡 3) F Z)
    (s := univ) (t := univ) (x₀ := p)
    (N.cover_local_diffeomorph.contMDiff.mdifferentiable (by simp) _).mdifferentiableWithinAt
    (fun _ _ => mem_univ _) (uniqueMDiffWithinAt_univ (𝓡 3)) hcyl
  simp only [mpullbackWithin_univ] at hfirst hsecond
  simpa only [twistedChartLift, mpullback_eq_pullback] using! (hfirst.trans hsecond).symm

end PoincareConjecture.M35
