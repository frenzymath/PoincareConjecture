import PoincareLib.Geometry.CurveShortening.Comparison.Theory
import PoincareLib.Geometry.CurveShortening.Comparison.CompleteComparison
import PoincareLib.Geometry.CurveShortening.Comparison.DiskAdapters
import PoincareLib.Geometry.CurveShortening.Comparison.FamilyAdapters
import PoincareLib.Geometry.CurveShortening.Ramp.Main

/-!
# M64 polygon approximation and annulus comparison proof entry

The complete construction consumes the exact M63 theorem once. The checked
assembly retains the original comparison, evolution and family statements
on the same actual geometry.

Morgan--Tian context: Chapter 19, Sections 19.3-19.7, printed pp. 447-481; the frozen M64
contracts and project comparison erratum specify the final interfaces.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- M64: given M63's complete ramp-estimate theorem, every C1 loop in a
compact Hausdorff second-countable smooth three-manifold with an actual
metric and compatible connection has a sampled minimizing N-gon for every
positive N. On each compact C1 set and for each zeta>0, one N0 works for
every N>=N0 and every loop: the polygon map is unique, its length is the
sum of its side lengths, its nonnegative length loss is less than zeta,
and an actual piecewise C1 short-geodesic annulus has area less than zeta.
Constant sides are allowed; the raw polygon need not be C1 at its corners.

Every raw continuous sphere family of null C1 loops admits these polygons
continuously for every sufficiently large N, with actual raw null boundaries,
nonempty filling classes and filling-area error less than zeta. Fixed-profile
flattening gives an actual homotopic C1 family, smooth in the angular variable,
with continuous first and second angular jets and the same length/area bounds.

For each compact smooth Ricci flow on [a,b] in dimension n>=3, choose one
actual M63 geometry, with constants and circle products before circumference
or curve. Two C2 shrinking ramps of initial degree one, joined by an actual
initial annulus, have nonempty annular area classes at all included times.
Their nonnegative infimum mu is continuous on [a,b]. For a<=t<b its upper
forward derivative is at most (2*n-1)*RmSup(t)*mu(t), where RmSup is the
actual full curvature norm supremum. For a<=s<=t<=b it also satisfies
mu(t)<=exp((2*n-1)*K0*(t-s))*mu(s), with the separate original unit-input
bound K0. No equality between K0 and the full norm is asserted.

For every r>0 choose a positive area threshold before circumference, time
and curves. Any two periodic C2 positive-slope ramps, of arbitrary positive
degree, obey L1>=3*L0/4 if L0>=r, every first-curve subarc of length at most
r has total curvature less than 1/200, and an actual joining annulus has
area below that threshold. The intrinsic counterpart holds for every
0<delta<1/100, r>0 and real Gaussian upper bound K: choose mu>0 before
the annulus; L0>r, absolute boundary turning less than delta on all subarcs
of length at most r, Gaussian curvature at most K and area<mu imply the
same length comparison.

Projection gives the literal base annulus and does not increase its area.
In dimension three it glues disks in both quantified directions, with the
projected annulus area and arbitrary positive slack. Nonempty disk classes
then give the absolute filling-infimum comparison. Every raw continuous C1
sphere family has finitely many actual parameter nodes and one positive
circumference cutoff; each member uses one node for all smaller positive
circumferences, with an actual annulus of any prescribed positive area bound.

On the same three-dimensional geometry, the every-N approximation retains
its exact M63 solution family, initial/global length and total-curvature
bounds, and uniform intrinsic derivative estimates. Applied curve estimates
use those same solutions and K0,K1,K2. In particular their energy is
integrable, and for circumference<1 is bounded by
(sup(initial base lengths)+1)*exp(K2*(b-a)), as the checked family adapter
shows. Apply m64EvolvingApproximation_from_M63 to each supplied static
N-gon approximation; its checked equality retains that literal record.

Sources: Morgan--Tian Definition 19.18, Claims 19.19-19.20 and Corollary
19.21, pp. 450-451; Lemma 19.17 and Claim 19.22, pp. 449-453; Lemma
19.15 and Corollary 19.16, pp. 447-449; Lemma 19.31, pp. 462, 464-466;
Proposition 19.35, pp. 467-481; finite nets and disk comparisons, pp. 461-466.
Retain the 2015 Section 19.2 correction, pp. 8-9. The annular existence and
regularity route uses Morrey's ICM1950 lecture, AMS1952 pp. 181-185, and
Lemaire1982 Theorem 1.7, p. 94, with Remark 5.5, p. 102. The source-class
transports, harmonic-circle branch exclusion, initial-homotopy guard,
endpoint passage, norm distinction, focusing and length-loss repairs are
owned here; see reviews/contracts/M64-round1.md and
reviews/errata/2026-09-14-m64-annulus-comparison.md. -/
theorem m64AnnulusComparison (hM63 : M63RampEstimatesTheory.{u}) :
    M64ComparisonTheory.{u} := by
  exact m64ComparisonTheory_from_M63 hM63

/-- Concrete predecessor application; no additional admission is introduced. Source:
Morgan--Tian (2007), Chapter 19, Sections 19.3-19.7, pp. 447-481; frozen M64 comparison
contract and `reviews/errata/2026-09-14-m64-annulus-comparison.md`. -/
theorem m64AnnulusComparison_from_predecessors : M64ComparisonTheory.{u} :=
  m64AnnulusComparison m63RampEstimates_from_predecessors

end PoincareMT
