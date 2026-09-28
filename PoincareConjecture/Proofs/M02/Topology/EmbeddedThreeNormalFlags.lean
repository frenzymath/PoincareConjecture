import PoincareConjecture.Proofs.M02.Topology.EmbeddedThreeFlagCarrier
import PoincareConjecture.Proofs.M02.Topology.GeometricFlagBounds
import PoincareConjecture.Proofs.M02.Topology.NormalFiberContraction

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped BigOperators Manifold ContDiff Topology NNReal

universe u

namespace PoincareConjecture.Proofs.M02.Topology.EmbeddedThreeFlagGrid

variable {N : Nat} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace Real (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {e : C(M, EuclideanSpace Real (Fin N))} {epsilon : NNReal}
  (G : EmbeddedThreeFlagGrid e epsilon)

def localComparison (p : M) : EuclideanSpace Real (Fin N) → EuclideanSpace Real (Fin N) :=
  finiteFlagComparison (G.localTangentCenter p) (G.localManifoldCenter p)
    (G.localTangentFlag_injective p)

set_option maxHeartbeats 3000000 in

theorem exists_local_normal_flag_point (p : M) (kappa : NNReal) (hkappa : kappa < 1)
    (hcoefficient :
      96 * (N + 1 : Real) ^ 2 * (epsilon : Real) / ambientGridGap N (N - 4) *
        ((1 + (ambientGridGap N (N - 4) /
          (4 * (N + 1 : Real) * (2 : Real) ^ (N + 1)))⁻¹) ^ 4 - 1) ≤
            (kappa : Real)) :
    ∃ y : EuclideanSpace Real (Fin N),
      y ∈ Set.range (finiteOrderComplexMap (G.localFaces p) (G.localManifoldCenter p)) ∧
      ‖y - e p‖ ≤ 2 * (N + 1 : Real) * G.h ∧
      (embeddedThreeTangent e p).orthogonalProjectionOnto (y - e p) = 0 ∧
      ∀ x : EuclideanSpace Real (Fin N),
        normalAffineConstraint (embeddedThreeTangent e p) (e p) x = 0 →
        ‖x - e p‖ ≤ 4 * (N + 1 : Real) * G.h →
        (embeddedThreeTangent e p).orthogonalProjectionOnto
          (G.localComparison p x - e p) = 0 → G.localComparison p x = y := by
  classical
  let E := EuclideanSpace Real (Fin N)
  let T := embeddedThreeTangent e p
  let L : Real := N + 1
  let b : Real := ambientGridGap N (N - 4)
  let eta : Real := b / (4 * L * (2 : Real) ^ (N + 1))
  let delta : Real := 24 * L ^ 2 * (epsilon : Real) * G.h / b
  let U : Set E := {x | normalAffineConstraint T (e p) x = 0} ∩
    closedBall (e p) (4 * L * G.h)
  have hL : 0 < L := by dsimp [L]; positivity
  have hb : 0 < b := by
    dsimp [b, ambientGridGap, ambientGridMoveRatio, ambientGridSlabRatio]
    positivity
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hh : 0 < G.h := G.h_pos
  have hdelta : 0 ≤ delta := by dsimp [delta]; positivity
  have heps : (epsilon : Real) * (1000 * L) ≤ b :=
    (le_div_iff₀ (by positivity : (0 : Real) < 1000 * L)).mp G.epsilon_small
  have hdeltar : delta ≤ L * G.h := by
    apply (div_le_iff₀ hb).mpr
    have hmul := mul_le_mul_of_nonneg_right heps (mul_pos hL hh).le
    have hnonneg : 0 ≤ L ^ 2 * (epsilon : Real) * G.h := by positivity
    nlinarith
  have hU : Convex Real U :=
    ((convex_singleton (0 : Tᗮ)).affine_preimage
      (normalAffineConstraint T (e p))).inter (convex_closedBall _ _)
  have hUr : U ⊆ Set.range
      (finiteOrderComplexMap (G.localFaces p) (G.localTangentCenter p)) := by
    intro x hx
    exact G.localTangentFlag_covers_disk p x hx.1
      (by
        have hd := mem_closedBall.mp hx.2
        rw [dist_eq_norm x (e p)] at hd
        exact hd)
  have hbound : delta / (G.h / 4) * ((1 + eta⁻¹) ^ 4 - 1) ≤ (kappa : Real) := by
    have heq : delta / (G.h / 4) = 96 * L ^ 2 * (epsilon : Real) / b := by
      dsimp [delta]
      field_simp [ne_of_gt hh, ne_of_gt hb]
      ring
    rw [heq]
    exact hcoefficient
  have hlip : LipschitzOnWith kappa (fun x => G.localComparison p x - x) U := by
    apply geometricFlagComparison_displacement_lipschitzOn
      (fun s : G.localFaces p => s.val) (fun _ _ => Iff.rfl)
      (fun s => G.K.nonempty_of_mem_faces s.property.1.1)
      (G.h / 4) (by positivity) ?_
      (G.localTangentCenter p) (G.localManifoldCenter p) eta heta
      (fun s => (G.localTangentCenter_spec p s).2.1)
      delta hdelta (fun s => (G.localTangentCenter_spec p s).2.2)
      4 (G.local_chain_card_le_four p) (G.localTangentFlag_injective p)
      kappa hbound U hU hUr
    intro s v hv
    have hcard : 2 ≤ s.val.card := by
      have hlow := (G.centers s s.property.1.1 s.property.1.2).1
      have hN := G.ambient_dimension
      omega
    simpa only [Finset.coe_erase] using
      (G.geometry s s.property.1.1).2.2 hcard v hv
  have herr (x : E) (hx : x ∈ U) : ‖G.localComparison p x - x‖ ≤ L * G.h :=
    (finiteFlagComparison_displacement_le (G.localTangentCenter p) (G.localManifoldCenter p)
      (G.localTangentFlag_injective p) delta
      (fun s => (G.localTangentCenter_spec p s).2.2) x (hUr hx)).trans hdeltar
  have htranslate (v : T) (hv : ‖v‖ ≤ 4 * L * G.h) : e p + (v : E) ∈ U := by
    refine ⟨?_, ?_⟩
    · change Tᗮ.orthogonalProjectionOnto (e p + (v : E) - e p) = 0
      rw [add_sub_cancel_left]
      exact T.orthogonalProjectionOnto_orthogonal_apply_eq_zero v.property
    · apply mem_closedBall.mpr
      rw [dist_eq_norm (e p + (v : E)) (e p), add_sub_cancel_left]
      exact hv
  let f (v : T) := G.localComparison p (e p + (v : E))
  have herror (v : T) : f v - e p - (v : E) =
      G.localComparison p (e p + (v : E)) - (e p + (v : E)) := by
    dsimp only [f]
    abel
  have hferror (v : T) (hv : ‖v‖ ≤ 4 * L * G.h) :
      ‖f v - e p - (v : E)‖ ≤ L * G.h := by
    rw [herror]
    exact herr _ (htranslate v hv)
  have hflip : LipschitzOnWith kappa
      (fun v : T => f v - e p - (v : E)) (closedBall 0 (4 * L * G.h)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro v hv w hw
    rw [herror, herror]
    have h := hlip.dist_le_mul _ (htranslate v (mem_closedBall_zero_iff.mp hv))
      _ (htranslate w (mem_closedBall_zero_iff.mp hw))
    rw [dist_add_left] at h
    exact h
  have hr : 0 < L * G.h := mul_pos hL hh
  have hrR : L * G.h ≤ 4 * L * G.h := by nlinarith
  obtain ⟨v, hv, hnormal, huniq⟩ := exists_unique_normal_fiber_point T (e p)
    (L * G.h) (4 * L * G.h) hr hrR f kappa hkappa hferror hflip
  refine ⟨f v, ?_, ?_, hnormal, ?_⟩
  · exact finiteFlagComparison_mem_range (G.localTangentCenter p) (G.localManifoldCenter p)
      (G.localTangentFlag_injective p) _ (hUr (htranslate v (hv.trans hrR)))
  · have hd := hferror v (hv.trans hrR)
    have htri := norm_add_le (f v - e p - (v : E)) (v : E)
    rw [sub_add_cancel, Submodule.norm_coe] at htri
    change ‖f v - e p‖ ≤ 2 * L * G.h
    linarith
  · intro x hplane hx hnormalx
    have hxT : x - e p ∈ T := by
      change Tᗮ.orthogonalProjectionOnto (x - e p) = 0 at hplane
      have h := Tᗮ.orthogonalProjectionOnto_eq_zero_iff.mp hplane
      simpa only [T.orthogonal_orthogonal] using h
    let w : T := ⟨x - e p, hxT⟩
    have hxw : e p + (w : E) = x := add_sub_cancel _ _
    have hw : ‖w‖ ≤ 4 * L * G.h := hx
    have hwzero : T.orthogonalProjectionOnto (f w - e p) = 0 := by
      simpa only [f, hxw] using hnormalx
    have hwv := huniq w hw hwzero
    change G.localComparison p x = f v
    rw [← hxw]
    exact congrArg f hwv

end PoincareConjecture.Proofs.M02.Topology.EmbeddedThreeFlagGrid
