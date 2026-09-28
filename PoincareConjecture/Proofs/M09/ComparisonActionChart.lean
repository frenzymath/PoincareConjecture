import PoincareConjecture.Proofs.M09.ComparisonEndpointInverse
import PoincareConjecture.Proofs.M09.ActionCongruence
import PoincareConjecture.Proofs.M09.PathComparison
import PoincareConjecture.Definitions.Ch06.ReducedLength
import Mathlib.Geometry.Manifold.Algebra.LieGroup

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

set_option maxHeartbeats 1600000 in

set_option backward.isDefEq.respectTransparency false in
theorem exists_upperBarrier_of_comparison_family
    (hM04 : RicciFlowCurvatureTheory.{u}) (hL : LGeodesicTheory F T τmax)
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (A : LExponentialFamily F T τmax p) (Z : TangentSpace (𝓡 n) p)
    (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (hmin : IsMinimizingBackwardLPath F T 0 b (A.path Z b hb hmax))
    (f : E × ℝ → M) (Ω : Set (E × ℝ)) (hΩ : IsOpen Ω)
    (hf : ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞ f Ω)
    (hsegment : ∀ s ∈ Set.Icc 0 (Real.sqrt b), ((0 : E), s) ∈ Ω)
    (hbase : ∀ s, f (0, s) = A.squareFamily Z s)
    (hfixed : ∀ x, f (x, 0) = p)
    (hbij : Function.Bijective (mfderiv (𝓘(ℝ, E)) (𝓡 n)
      (fun x ↦ f (x, Real.sqrt b)) 0)) :
    ∃ (B : ReducedLengthUpperBarrier F T p (A.gamma Z b) b)
      (e : OpenPartialHomeomorph (E × ℝ) (M × ℝ)),
      ((0 : E), b) ∈ e.source ∧
      e.source ⊆ squareFamilyParameterDomain Ω τmax ∧
      Set.EqOn e (fun z ↦ (f (z.1, Real.sqrt z.2), z.2)) e.source ∧
      B.neighborhood = e.target ∧
      ContMDiffOn ((𝓡 n).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, ℝ)) ∞
        B.representative B.neighborhood ∧
      ∀ z ∈ e.source, B.representative (f (z.1, Real.sqrt z.2), z.2) =
        backwardLLength F T 0 z.2 (fun t ↦ f (z.1, Real.sqrt t)) /
          (2 * Real.sqrt z.2) := by
  let S := squareFamilyParameterDomain Ω τmax
  have hzS : ((0 : E), b) ∈ S := by
    refine ⟨⟨hb, hmax⟩, fun r hr ↦ hsegment _ ?_⟩
    exact ⟨mul_nonneg (Real.sqrt_nonneg _) hr.1,
      mul_le_of_le_one_right (Real.sqrt_nonneg _) hr.2⟩
  obtain ⟨e, hze, hsub, he, hinv⟩ := exists_squareFamily_endpoint_inverse
    f Ω hΩ hf τmax ((0 : E), b) hzS hbij
  have hendpoint : f (0, Real.sqrt b) = A.gamma Z b := by
    rw [hbase, A.square_agrees Z (Real.sqrt b)
      ⟨Real.sqrt_nonneg _, Real.sqrt_lt_sqrt hb.le hmax⟩, Real.sq_sqrt hb.le]
  have hecenter : e (0, b) = (A.gamma Z b, b) := by
    simpa only [hendpoint] using he hze
  have hcenter_mem : (A.gamma Z b, b) ∈ e.target := hecenter ▸ e.map_source hze
  have hinvcenter : e.symm (A.gamma Z b, b) = (0, b) := by
    rw [← hecenter, e.left_inv hze]
  let Q : E × ℝ → ℝ := fun z ↦
    backwardLLength F T 0 z.2 (fun t ↦ f (z.1, Real.sqrt t)) / (2 * Real.sqrt z.2)
  have hQ : ContDiffOn ℝ ∞ Q S := by
    intro z hz
    have hLsm := contDiffAt_smoothSquareFamily_action F hM04 T τmax hτmax hwindow
      f Ω hΩ hf z hz.1 hz.2
    exact (hLsm.div (contDiffAt_const.mul (contDiffAt_snd.sqrt hz.1.1.ne'))
      (mul_ne_zero two_ne_zero (Real.sqrt_pos.mpr hz.1.1).ne')).contDiffWithinAt
  let C : M × ℝ → ℝ := fun w ↦ Q (e.symm w)
  have hC : ContMDiffOn ((𝓡 n).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, ℝ)) ∞ C e.target :=
    hQ.contMDiffOn.comp hinv (fun w hw ↦ hsub (e.map_target hw))
  have hcompare (z : E × ℝ) (hz : z ∈ S) :
      reducedLength F T p (f (z.1, Real.sqrt z.2)) z.2 ≤ Q z := by
    let D := (fun s : ℝ ↦ (z.1, s)) ⁻¹' Ω
    have hD : IsOpen D := hΩ.preimage (continuous_const.prodMk continuous_id)
    have hKD : Set.Icc 0 (Real.sqrt z.2) ⊆ D := by
      intro s hs
      have hc : 0 < Real.sqrt z.2 := Real.sqrt_pos.mpr hz.1.1
      have hr : s / Real.sqrt z.2 ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨div_nonneg hs.1 hc.le, (div_le_one hc).mpr hs.2⟩
      change (z.1, s) ∈ Ω
      simpa only [mul_div_cancel₀ s hc.ne'] using hz.2 (s / Real.sqrt z.2) hr
    have hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (fun s ↦ f (z.1, s)) D :=
      hf.comp (contDiff_const.prodMk contDiff_id).contMDiff.contMDiffOn (fun _ hs ↦ hs)
    obtain ⟨P, hP, _⟩ := exists_backwardPath_of_smoothSquareCurve F hM04 T τmax hτmax
      hwindow z.2 hz.1.1 hz.1.2 (fun s ↦ f (z.1, s)) D hD hKD hα
    have hP0 : P.curve 0 = p := by simp only [hP, Real.sqrt_zero, hfixed]
    have hPe : P.curve z.2 = f (z.1, Real.sqrt z.2) := congrFun hP z.2
    have h := reducedLength_le_path hL hz.1.1 hz.1.2.le P hP0 hPe
    simpa only [hP, Q] using h
  have htouch : C (A.gamma Z b, b) = reducedLength F T p (A.gamma Z b) b := by
    change Q (e.symm (A.gamma Z b, b)) = _
    rw [hinvcenter]
    have hact : backwardLLength F T 0 b (fun t ↦ f (0, Real.sqrt t)) = A.action Z b := by
      apply backwardLLength_congr_Ioo F T 0 b hb.le
      intro t ht
      change f (0, Real.sqrt t) = A.gamma Z t
      rw [hbase, A.square_agrees Z (Real.sqrt t)
        ⟨Real.sqrt_nonneg _, Real.sqrt_lt_sqrt ht.1.le (ht.2.trans hmax)⟩,
        Real.sq_sqrt ht.1.le]
    have hminvalue := reducedLength_eq_minimizing_path (p := p) (q := A.gamma Z b)
      hL hb hmax.le (A.path Z b hb hmax)
      (by rw [A.path_eq]; exact A.gamma_at_zero Z) (by rw [A.path_eq]) hmin
    rw [A.path_eq] at hminvalue
    exact (congrArg (fun a : ℝ ↦ a / (2 * Real.sqrt b)) hact).trans hminvalue.symm
  have hdom (w : M × ℝ) (hw : w ∈ e.target) : reducedLength F T p w.1 w.2 ≤ C w := by
    have hcoords : (f ((e.symm w).1, Real.sqrt (e.symm w).2), (e.symm w).2) = w :=
      (he (e.map_target hw)).symm.trans (e.right_inv hw)
    have h := hcompare (e.symm w) (hsub (e.map_target hw))
    change reducedLength F T p w.1 w.2 ≤ Q (e.symm w)
    convert h using 1
    exact congrArg₂ (fun x t ↦ reducedLength F T p x t)
      (congrArg Prod.fst hcoords).symm (congrArg Prod.snd hcoords).symm
  have hcenter := hC.contMDiffAt (e.open_target.mem_nhds hcenter_mem)
  have htime : ∃ d : ℝ, HasDerivAt (fun t ↦ C (A.gamma Z b, t)) d b := by
    have h := (hcenter.comp b (contMDiffAt_const.prodMk contMDiffAt_id)).contDiffAt
    exact ⟨_, (h.differentiableAt (by simp)).hasDerivAt⟩
  let B : ReducedLengthUpperBarrier F T p (A.gamma Z b) b := {
    neighborhood := e.target
    neighborhood_open := e.open_target
    center_mem := hcenter_mem
    representative := C
    touches := htouch
    dominates := hdom
    representative_spacetime_smooth := hcenter
    representative_space_smooth_on := hC.comp
      (contMDiffOn_id.prodMk contMDiffOn_const) (fun _ hx ↦ hx)
    representative_space_smooth := hcenter.comp (A.gamma Z b)
      (contMDiffAt_id.prodMk contMDiffAt_const)
    representative_time_derivative := htime
  }
  refine ⟨B, e, hze, hsub, he, rfl, hC, ?_⟩
  intro z hz
  change Q (e.symm (f (z.1, Real.sqrt z.2), z.2)) = Q z
  have hez : e z = (f (z.1, Real.sqrt z.2), z.2) := he hz
  rw [← hez, e.left_inv hz]

end PoincareConjecture.Proofs.M09
