import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.Stability.StablePrefix
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.InitialValue.InitialVector

/-!
# Recovering a confined minimizer from a fixed stable prefix

An actual square Euler path is a branch of the supplied exponential
family. If its minimizing prefix reaches a fixed stable endpoint, the
stable slice's uniqueness identifies its initial vector. This step
uses fixed-time stability only. Morgan-Tian Lemma 6.18 and Proposition
6.30, pp. 114, 118-119, in the proof of Proposition 6.56, p. 133.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T b τ : ℝ} {x y : G.Point}

private theorem initialValuePath_cast_curve {c : ℝ} {Z : G.Horizontal x}
    (h : b = c) (P : M14SquareRootInitialValuePath G T b x y Z) :
    (h ▸ P : M14SquareRootInitialValuePath G T c x y Z).path.curve = P.path.curve := by
  cases h
  rfl

/-- Every actual zero-start square Euler path belongs to the supplied
exponential family, with its actual transported initial velocity.
Lemma 6.18, p. 114. -/
theorem exists_exponential_branch_of_square_euler (E : M14ExponentialFamily G T x)
    {p : M14BackwardPath G T 0 b x y} (R : M14SquareRootPath G p)
    (ER : M14PullbackExtension G R.curve (M14SqrtParameterInterval 0 b)
      R.horizontal_velocity)
    (hEuler : ∀ s ∈ M14SqrtParameterInterval 0 b, ∀ W,
      M14SquareRootEulerResidual G R ER s W = 0) :
    ∃ Z : G.Horizontal x, (Z, Real.sqrt b) ∈ E.domain ∧
      EqOn p.curve (fun t => E.gamma Z (Real.sqrt t)) (Icc 0 b) := by
  have hb : 0 < b := p.tau_lt
  have hzero : (0 : ℝ) ∈ M14SqrtParameterInterval 0 b := by
    exact ⟨by simp, Real.sqrt_nonneg b⟩
  have h0 : R.curve 0 = x := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      (R.agrees 0 hzero).trans (by simpa using p.curve_start)
  let Z : G.Horizontal x := (1 / 2 : ℝ) • (h0 ▸ R.horizontal_velocity 0)
  let P : M14SquareRootInitialValuePath G T b x y Z := {
    path := p
    square_path := R
    extension := ER
    euler := hEuler
    initial_velocity := ⟨h0, by
      dsimp only [Z]
      rw [smul_smul]
      norm_num⟩ }
  let P' : M14SquareRootInitialValuePath G T ((Real.sqrt b) ^ 2) x y Z :=
    (Real.sq_sqrt hb.le).symm ▸ P
  have hPcurve : P'.path.curve = p.curve :=
    initialValuePath_cast_curve (Real.sq_sqrt hb.le).symm P
  refine ⟨Z, (E.positive_survival_iff Z (Real.sqrt b) (Real.sqrt_pos.mpr hb)).mpr
    ⟨y, ⟨P'⟩⟩, ?_⟩
  simpa only [hPcurve, Real.sq_sqrt hb.le] using
    E.initial_value_agreement Z (Real.sqrt b) (Real.sqrt_pos.mpr hb) y P'

private theorem minimizing_curves_eqOn_of_endpoint_eq {z w : G.Point}
    (p : M14BackwardPath G T 0 τ x z) (q : M14BackwardPath G T 0 τ x w)
    (h : z = w)
    (hunique : ∀ r : M14BackwardPath G T 0 τ x z,
      M14IsMinimizing r → EqOn r.curve p.curve (Icc 0 τ))
    (hq : M14IsMinimizing q) : EqOn q.curve p.curve (Icc 0 τ) := by
  cases h
  exact hunique q hq

/-- A minimizing path whose strict prefix reaches a fixed stable
endpoint has the same initial vector as that stable branch. No
future joint stability is presumed, Proposition 6.30, pp. 118-119. -/
theorem initialVector_eq_of_minimizing_stable_prefix
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (E : M14ExponentialFamily G T x)
    (H : M14StableSet G T τ x E) {Z W : G.Horizontal x} (hZ : Z ∈ H.carrier)
    (p : M14BackwardPath G T 0 b x y) (hp : M14IsMinimizing p)
    (hW : (W, Real.sqrt b) ∈ E.domain) (hτb : τ < b)
    (hcurve : EqOn p.curve (fun t => E.gamma W (Real.sqrt t)) (Icc 0 b))
    (hpoint : p.curve τ = H.endpoint_map Z) : W = Z := by
  obtain ⟨q, hqcurve, _, hqunique⟩ := H.minimizing_path Z hZ
  have hprefix := isMinimizing_prefixPath hM12 p hp ⟨H.tau_pos, hτb⟩
  have heq := minimizing_curves_eqOn_of_endpoint_eq q
    (prefixPath p τ H.tau_pos hτb.le) hpoint.symm hqunique hprefix
  have hWτ : (W, Real.sqrt τ) ∈ E.domain :=
    (E.maximal_lifetime W).out (E.domain_zero W) hW
      ⟨Real.sqrt_nonneg τ, Real.sqrt_le_sqrt hτb.le⟩
  apply initialVector_eq_of_backward_branches_eqOn E hWτ
    (H.survivor Z hZ) (Real.sqrt_pos.mpr H.tau_pos)
  rw [Real.sq_sqrt H.tau_pos.le]
  intro t ht
  exact (hcurve ⟨ht.1, ht.2.trans hτb.le⟩).symm.trans
    ((heq ht).trans (hqcurve ht))

/-- A supplied stable branch minimizes at every positive earlier
time, including the stable terminal time itself, Proposition 6.30,
pp. 118-119. -/
theorem exponentialPath_minimizing_of_stable_prefix
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) (H : M14StableSet G T τ x E)
    {Z : G.Horizontal x} (hZ : Z ∈ H.carrier) {s : ℝ}
    (hs : 0 < s) (hst : s ^ 2 ≤ τ) (hD : (Z, s) ∈ E.domain) :
    M14IsMinimizing (E.path Z s hD hs) := by
  obtain ⟨_, _, U, _, hZU, hbranch⟩ := (H.carrier_exact Z).mp hZ
  apply exponentialPath_minimizing_of_uniqueBranch E hs hD
  rcases lt_or_eq_of_le hst with hlt | heq
  · exact uniqueMinimizingBranch_prefix hM04 hCoordinates hM12 E
      (sq_pos_of_pos hs) hlt (hbranch Z hZU)
  · simpa only [heq] using hbranch Z hZU

end PoincareMT.M14
