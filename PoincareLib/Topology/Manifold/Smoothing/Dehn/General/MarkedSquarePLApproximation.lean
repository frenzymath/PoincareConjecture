import PoincareLib.Topology.Manifold.Smoothing.Dehn.General.PLDomainMarkedApproximation
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.MarkedBoundaryPLLoopDisk
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Isotopy.Mathlib.HomotopyLoopWhisker
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Handles.HamiltonHandleCubeBall

/-!
# Approximate the literal square pair and retain its excluded rim class

The original continuous filling and entire prescribed rim construct
one chartwise PL square map. Its actual whole-rim homotopy stays in
the same original marked surface. The homotopy's basepoint trace
retains exclusion from the original subgroup in the fixed path order.
See Hatcher, Theorem 3.1, pp. 45--48, and Dehn derivations 020,
022 section 3 and 023 section 4. No disk embedding or interior
properness is asserted at this initialization step.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]

/-- The arbitrary continuous square pair produces an actual PL pair
in the same original region and marked surface. The whole rim and
its explicit basepoint transport retain the original excluded class.
See Dehn derivation 023, section 4; no input rim regularity is used. -/
theorem exists_marked_PL_square_pair
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} (he : PLDomain e R)
    (F : Set X) (hF : F ⊆ frontier R)
    (hFopen : IsOpen ((Subtype.val : frontier R → X) ⁻¹' F))
    (f : C(D, R)) (gamma : C(Q, F))
    (hpair : ∀ x : Q,
      (f ⟨x.val, sphere_subset_closedBall x.property⟩ : X) = (gamma x : X))
    (J : Subgroup (FundamentalGroup F (gamma squareRimBase)))
    (houtside : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map gamma.continuous)) ∉ J) :
    ∃ (g : V2 → X) (gamma₀ : C(Q, F)),
      PolyhedralPLInCharts e g D ∧ MapsTo g D R ∧
      (∀ x : Q, g x.val = (gamma₀ x : X)) ∧
      ∃ H : gamma.Homotopy gamma₀,
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (((H.evalAt squareRimBase).trans (squareRimLoop.map gamma₀.continuous)).trans
            (H.evalAt squareRimBase).symm)) ∉ J := by
  classical
  obtain ⟨_, _, _, _, _, _, hmodel, _⟩ := isFinitePLBallPair_unit_cube (ι := Fin 2)
  obtain ⟨_, ⟨S, hS, hSD, _⟩, _⟩ := hmodel
  let inc : C(Q, D) :=
    ⟨fun x => ⟨x.val, sphere_subset_closedBall x.property⟩,
      continuous_subtype_val.subtype_mk _⟩
  let B : Set D := (Subtype.val : D → V2) ⁻¹' Q
  have hB : IsCompact B := (isClosed_sphere.preimage continuous_subtype_val).isCompact
  have hBF : MapsTo (fun x : D => (f x : X)) B F := by
    intro x hx
    change (f ⟨x.val, x.property⟩ : X) ∈ F
    rw [hpair ⟨x.val, hx⟩]
    exact (gamma ⟨x.val, hx⟩).property
  obtain ⟨g, a, hg, hga, eta, heta⟩ := he.exists_marked_PL_approximation
    D ⟨S, hS, hSD⟩ (inc squareRimBase) f B hB F hF hFopen hBF
  have haF (x : Q) : (a (inc x) : X) ∈ F := by
    have h := heta 1 (inc x) x.property
    have hval : (eta (1, inc x) : X) = (a (inc x) : X) :=
      congrArg (fun y : R => (y : X)) (eta.map_one_left (inc x))
    exact hval ▸ h
  let gamma₀ : C(Q, F) :=
    ⟨fun x => ⟨(a (inc x) : X), haF x⟩,
      (continuous_subtype_val.comp (a.continuous.comp inc.continuous)).subtype_mk _⟩
  let H : gamma.Homotopy gamma₀ :=
    { toFun := fun z => ⟨(eta (z.1, inc z.2) : X), heta z.1 (inc z.2) z.2.property⟩
      continuous_toFun := (continuous_subtype_val.comp
        (eta.continuous.comp (continuous_fst.prodMk
          (inc.continuous.comp continuous_snd)))).subtype_mk _
      map_zero_left := by
        intro x
        apply Subtype.ext
        change (eta (0, inc x) : X) = (gamma x : X)
        exact (congrArg (fun y : R => (y : X)) (eta.map_zero_left (inc x))).trans (hpair x)
      map_one_left := by
        intro x
        apply Subtype.ext
        change (eta (1, inc x) : X) = (a (inc x) : X)
        exact congrArg (fun y : R => (y : X)) (eta.map_one_left (inc x)) }
  refine ⟨g, gamma₀, hg, ?_, ?_, H, ?_⟩
  · intro x hx
    rw [hga ⟨x, hx⟩]
    exact (a ⟨x, hx⟩).property
  · intro x
    exact hga (inc x)
  · have heq := H.loop_quotient_eq_whisker squareRimLoop
    change Path.Homotopic.Quotient.mk
      (((H.evalAt squareRimBase).trans (squareRimLoop.map gamma₀.continuous)).trans
        (H.evalAt squareRimBase).symm) ∉ J
    rw [← heq]
    exact houtside

end PoincareMT.M76.Dehn
