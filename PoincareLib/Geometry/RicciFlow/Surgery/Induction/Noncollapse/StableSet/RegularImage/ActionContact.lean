import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.StableSet.RegularImage.SurvivalSlice
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Paths.Action.LLength
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# First-order contact at a differentiable minimizing endpoint

Morgan--Tian Claim 6.68 and Corollary 6.67, printed pp. 139-140.
Actual exponential action is an upper support of the minimum action
through the genuine survival slice map. At a minimizing branch the two
actions agree. Fermat's theorem therefore identifies their first
derivatives at each point where the minimum action is differentiable.
Neither stable minimality nor smoothness of the minimum is assumed.
-/

set_option autoImplicit false
-- The derivative comparison retains the selected horizontal metric instances.
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.Proofs.M46

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T tau : ℝ} {x : G.Point}

/-- On the finite action domain the selected surviving branch supplies
an actual competitor to its true slice endpoint, Definition 6.27 and
Claim 6.68, pp. 117 and 140. -/
theorem actionValue_le_survival_action
    (E : M14ExponentialFamily G T x) (htau : 0 < tau)
    (q0 : (G.slices (T - tau)).Point)
    {Z : G.Horizontal x} (hZ : (Z, Real.sqrt tau) ∈ E.domain)
    (hfinite : M14FiniteValueDomain G T 0 tau x
      (survivalSliceMap E tau htau.le q0 Z).val) :
    M14ActionValue G T 0 tau x (survivalSliceMap E tau htau.le q0 Z).val ≤
      E.action Z (Real.sqrt tau) := by
  have hfinite' : M14FiniteValueDomain G T 0 ((Real.sqrt tau) ^ 2) x
      (E.gamma Z (Real.sqrt tau)) := by
    rw [Real.sq_sqrt htau.le, ← survivalSliceMap_val E htau.le q0 hZ]
    exact hfinite
  have h := M14.actionValue_le_action hfinite'
    (E.path Z (Real.sqrt tau) hZ (Real.sqrt_pos.mpr htau))
  rw [← E.action_eq Z (Real.sqrt tau) hZ (Real.sqrt_pos.mpr htau),
    Real.sq_sqrt htau.le, ← survivalSliceMap_val E htau.le q0 hZ] at h
  exact h

/-- At an actual minimizing exponential branch its action is exactly
the minimum action at the true slice endpoint, Claim 6.68, p. 140. -/
theorem minimizing_survival_action_eq
    (E : M14ExponentialFamily G T x) (htau : 0 < tau)
    (q0 : (G.slices (T - tau)).Point)
    {Z : G.Horizontal x} (hZ : (Z, Real.sqrt tau) ∈ E.domain)
    (hmin : M14IsMinimizing (E.path Z (Real.sqrt tau) hZ (Real.sqrt_pos.mpr htau))) :
    E.action Z (Real.sqrt tau) =
      M14ActionValue G T 0 tau x (survivalSliceMap E tau htau.le q0 Z).val := by
  have h := E.action_global_eq Z (Real.sqrt tau) hZ (Real.sqrt_pos.mpr htau) hmin
  rwa [Real.sq_sqrt htau.le, ← survivalSliceMap_val E htau.le q0 hZ] at h

/-- Differentiability of the minimum action at one endpoint identifies
its pullback differential with actual branch action. Attainment in an
open neighborhood supplies the finite comparison domain, Claim 6.68,
p. 140. -/
theorem minimizing_action_contact_differential
    (LG : GeneralizedLGeometryConclusion G)
    (E : M14ExponentialFamily G T x) (htau : 0 < tau)
    (q0 : (G.slices (T - tau)).Point)
    {A : Set (G.slices (T - tau)).Point} (hA : IsOpen A)
    (hattained : ∀ q ∈ A, ∃ p : M14BackwardPath G T 0 tau x q.val,
      M14IsMinimizing p)
    {Z : G.Horizontal x} (hZ : (Z, Real.sqrt tau) ∈ E.domain)
    (hcenter : survivalSliceMap E tau htau.le q0 Z ∈ A)
    (hmin : M14IsMinimizing (E.path Z (Real.sqrt tau) hZ (Real.sqrt_pos.mpr htau)))
    (hlength : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ))
      (fun q : (G.slices (T - tau)).Point => M14ActionValue G T 0 tau x q.val)
      (survivalSliceMap E tau htau.le q0 Z)) :
    let metric := G.spacetime.horizontalMetric.toRiemannianMetric
    letI : NormedAddCommGroup (G.Horizontal x) :=
      (metric.toCore x).toNormedAddCommGroupOfTopology
        (metric.continuousAt x) (metric.isVonNBounded x)
    letI : InnerProductSpace ℝ (G.Horizontal x) :=
      .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
    letI : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
      ⟨metric⟩
    mfderiv (𝓘(ℝ, G.Horizontal x)) (𝓘(ℝ, ℝ))
      (fun W => E.action W (Real.sqrt tau)) Z =
      (mfderiv (𝓡 n) (𝓘(ℝ, ℝ))
        (fun q : (G.slices (T - tau)).Point => M14ActionValue G T 0 tau x q.val)
        (survivalSliceMap E tau htau.le q0 Z)).comp
          (mfderiv (𝓘(ℝ, G.Horizontal x)) (𝓡 n)
            (survivalSliceMap E tau htau.le q0) Z) := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  let f := survivalSliceMap E tau htau.le q0
  let L := fun q : (G.slices (T - tau)).Point => M14ActionValue G T 0 tau x q.val
  have hf := (survivalSliceMap_smooth E htau.le q0 hZ).mdifferentiableAt (by simp)
  have ha := (LG.exponential.action_differential T x E).2 Z (Real.sqrt tau) hZ
    (Real.sqrt_pos.mpr htau) |>.1
  have hcomposition := hlength.comp Z hf
  have heq : E.action Z (Real.sqrt tau) = L (f Z) :=
    minimizing_survival_action_eq E htau q0 hZ hmin
  have hlocal : IsLocalMin
      (fun W => E.action W (Real.sqrt tau) - L (f W)) Z := by
    filter_upwards [(survival_domain_open E (Real.sqrt tau)).mem_nhds hZ,
      hf.continuousAt.preimage_mem_nhds (hA.mem_nhds hcenter)] with W hW hWA
    change E.action Z (Real.sqrt tau) - L (f Z) ≤ _
    rw [heq, sub_self]
    obtain ⟨p, hp⟩ := hattained (f W) hWA
    exact sub_nonneg.mpr (actionValue_le_survival_action E htau q0 hW
      (M14.finiteValueDomain_of_minimizing p hp))
  have hzero := hlocal.hasFDerivAt_eq_zero
    (ha.hasMFDerivAt.hasFDerivAt.sub hcomposition.hasMFDerivAt.hasFDerivAt)
  exact (sub_eq_zero.mp hzero).trans (mfderiv_comp Z hlength hf)

end PoincareMT.Proofs.M46
