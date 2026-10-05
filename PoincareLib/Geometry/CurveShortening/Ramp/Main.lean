import PoincareLib.Geometry.CurveShortening.Comparison.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Ramp.Adapters
import PoincareLib.Geometry.CurveShortening.Ramp.Approximation.Profile
import PoincareLib.Geometry.CurveShortening.Ramp.CurveEstimates.Ambient.Geometry
import PoincareLib.Geometry.CurveShortening.Ramp.CurveEstimates.Analytic.Assembly
import PoincareLib.Geometry.CurveShortening.Ramp.Approximation.Family.ConclusionAssembly
import PoincareLib.Geometry.CurveShortening.Ramp.Approximation.Raw.Approximation
import PoincareLib.Geometry.CurveShortening.Ramp.Approximation.Family.Solutions
import PoincareLib.Geometry.CurveShortening.Ramp.LocalEstimates.Uniform.DerivativeEstimates
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Compatibility.ShortLoops
import PoincareLib.Geometry.RicciFlow.CurveShortening.CorrectedEvolution

/-!
# M63 complete ramp-estimate proof entry

The actual local theory, uniform estimates and approximation families fill
the frozen ramp theory. Earlier theorem services enter once here; the
conclusions retain the supplied primitive geometry and approximation records.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareMT

/-- The exact M58 small-loop disk conclusion used by the approximation proof. -/
theorem m63SmallLoopFillingService_from_M58 : M63SmallLoopFillingService.{u} :=
  repairedShortLoopTriviality.short_loop.small_loop_filling

/-- M63: given M58's small-loop disk service and M62's universal corrected
curve-evolution service, every Ricci flow on a compact Hausdorff second-countable
smooth manifold over [a,b] admits ambient bounds K0,K1,K2 and actual circle
products, with those bounds chosen before circumference and curve.

Every immersed periodic C2 initial curve has a local pure-normal solution
with its exact initial labels. Fixed-label uniqueness, continuous dependence,
intrinsic positive-time regularity and curvature-bounded continuation hold.
Continuation at b includes b without extending the ambient flow. Positive-time
C2 labels admit a fixed increasing C2 relabeling to a smooth geometric solution.
Smooth initial labels have the separate exact M62 branch.

For every positive-slope initial curve, of any positive winding degree, there
is a ramp solution throughout [a,b]. The exact slope equation gives positive
slope preservation before its sign-guarded lower inequality is used. The
regularized quotient h_epsilon/u retains its C1/u forcing term and gives a
finite curvature bound for each initial ramp. Length and total curvature have
the corrected exponential and integral bounds, including both endpoints and
both initial length and total curvature.

The fixed smooth profile flattens actual minimizing geodesic polygons.
Canonical graph ramps have degree one, horizontal velocity equal to side
speed times the profile, length at most the base length plus circumference,
and total curvature at most N*pi, allowing constant sides. Every continuous
raw sphere family of null C1 loops has such a smooth approximation, with
nonnegative length loss and filling-area error less than any 0<zeta<1, an
actual C1 homotopy and continuous first and second angular jets. For each
fixed positive circumference its actual solutions form a continuous family
whose base projection consists of null loops with the exact initial records.
For every supplied raw approximation at any positive tolerance, construct
this same family conclusion with approximation equal to the supplied record.
For each fixed circumference, continuation may depend on that circumference
and the initial C2 family; only the interior-jet constants below are uniform
in circumference. The original approximation-existence output is retained.

For nonnegative initial length and total-curvature bounds L0,Theta0, choose
local intrinsic jet constants before circumference, curve and family member.
They apply to every existing immersed shrinking curve with those initial
bounds and 0 < circumference < 1. Put delta = delta0*radius0^2. If a <= s,
0 < r < 1, L(s) >= r, every parameter subarc of length at most r at s has
total curvature at most delta, and s + delta*r^2 < b, then for
s < t < s + delta*r^2 and every i >= 0,
|D_s^i H|^2 <= C_i/(t-s)^(i+1). The supporting curvature bound instead uses
0 < r <= radius0, subarc total curvature at most delta0, and
s < t <= s + delta0*r^2 <= b; its upper bound is 2/(t-s). Neither estimate
requires the curve to be a ramp, and both exclude the reference time.

Sources: Morgan--Tian Claim 19.1, p. 437; Claims 19.11/19.22, Definition
19.12, Corollary 19.13 and Lemmas 19.14/19.17/19.24, pp. 446-455; the
supporting Lemma 19.58 and its proof, pp. 481-495; the 2015 Section 19.2
correction, (0.4), Lemma 0.4 and corrected comparisons, pp. 6-9. Local
analytic models are Altschuler--Grayson IMA823, Theorems 1.3/1.13, pp. 3-7,
and Altschuler IMA822, Theorem 3.1, pp. 4-6. Their moving-ambient C2
adaptations are owned here. Apply reviews/contracts/M63-round1.md and
reviews/errata/2026-09-14-m63-ramp-estimates.md, including the local parameter,
fixed-label and cutoff repairs. The overlapping M62 conclusions are applied
on the same restricted geometry; they receive no separate admission. -/
theorem m63RampEstimates (hM58 : M63SmallLoopFillingService.{u})
    (hM62 : M62CurveEvolutionTheory.{u}) : M63RampEstimatesTheory.{u} := by
  classical
  have construction : M63SmallLoopFillingService.{u} →
      M62CurveEvolutionTheory.{u} → M63RampEstimatesTheory.{u} := by
    intro _ h62
    have analytic {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
        [SecondCountableTopology M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        {a b : ℝ} (F : RicciFlow n M (Set.Icc a b))
        (hcompact : IsCompact (Set.univ : Set M)) (G : M63AmbientGeometry F) :
        M63AnalyticConclusion F G := by
      let : CompactSpace M := isCompact_univ_iff.mp hcompact
      apply m63AnalyticConclusion_of_local_uniform F hcompact h62 G
        (M63.localCurveTheory_of_compact F hcompact)
      · intro circumference hcirc
        let : Fact (0 < circumference) := ⟨hcirc⟩
        exact M63.localCurveTheory_of_compact (G.product circumference hcirc).flow isCompact_univ
      · exact m63UniformDerivativeEstimates_of_compact F hcompact h62 G
    refine ⟨fun _ hN => m63ProfileProperties hN, ?_, ?_, ?_⟩
    · intro n M _ _ _ _ _ a b F hcompact
      obtain ⟨G⟩ := m63AmbientGeometry_nonempty (F := F) h62 hcompact
      exact ⟨⟨G, analytic F hcompact G⟩⟩
    · intro M _ _ _ _ _ a b F hcompact G Gamma hnull zeta hzeta _hzeta1
      obtain ⟨A⟩ := m63RawApproximation_nonempty F hcompact Gamma hnull hzeta
      obtain ⟨C⟩ := m63FamilyConclusion_of_solutions G (analytic F hcompact G) A
        (fun circumference hcirc => Classical.choice
          (m63ProductSolutionFamily_nonempty F hcompact h62 G A circumference hcirc))
      exact ⟨C.1⟩
    · intro M _ _ _ _ _ a b F hcompact G Gamma _hnull zeta _hzeta A
      exact m63FamilyConclusion_of_solutions G (analytic F hcompact G) A
        (fun circumference hcirc => Classical.choice
          (m63ProductSolutionFamily_nonempty F hcompact h62 G A circumference hcirc))
  exact construction hM58 hM62

/-- Concrete predecessor assembly, with no extra proof placeholder. -/
theorem m63RampEstimates_from_predecessors : M63RampEstimatesTheory.{u} :=
  m63RampEstimates m63SmallLoopFillingService_from_M58
    m62CorrectedCurveEvolution_from_predecessors

end PoincareMT
