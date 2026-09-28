import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Triangulation.Sections.FiniteGraphSection
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Topology.OpenPartialHomeomorph.Basic

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped NNReal Topology

universe u v w

namespace Poincare.Topology

def normalAffineConstraint
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (T : Submodule Real E) [T.HasOrthogonalProjection]
    [Tᗮ.HasOrthogonalProjection] (p : E) : E →ᵃ[Real] Tᗮ :=
  Tᗮ.orthogonalProjectionOnto.toLinearMap.toAffineMap.comp
    ((AffineEquiv.vaddConst Real p).symm.toAffineMap)

theorem exists_unique_local_graph_section
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [FiniteDimensional Real E]
    {M : Type v} [TopologicalSpace M]
    {T : Submodule Real E} [T.HasOrthogonalProjection]
    (e : C(M, E)) (he : Function.Injective e) (p : M)
    (g : OpenPartialHomeomorph T M) (rho R a : Real) (epsilon : NNReal)
    (hgs : g.source = ball (0 : T) (2 * rho)) (hg0 : g 0 = p)
    (hgproj : ∀ v ∈ g.source,
      T.orthogonalProjectionOnto (e (g v) - e p) = v)
    (hglip : LipschitzOnWith epsilon
      (fun v : T => e (g v) - e p - (v : E)) g.source)
    (hgcover : ∀ q : M, dist (e q) (e p) < rho → q ∈ g.target)
    (ha : 0 < a) (hRrho : R < rho)
    (A : E →ᵃ[Real] Tᗮ) (s : Finset E)
    (hAeq : A = normalAffineConstraint T (e p))
    (hcard : s.card = Module.finrank Real Tᗮ + 1)
    (hgap : ∀ t : Finset E, t ⊆ s → t.card ≤ Module.finrank Real Tᗮ →
      ∀ x ∈ convexHull Real (t : Set E), a ≤ ‖A x‖)
    (x0 : E) (hx0 : x0 ∈ convexHull Real (s : Set E)) (hAx0 : A x0 = 0)
    (hsize : ∀ x ∈ convexHull Real (s : Set E), ‖x - e p‖ ≤ R)
    (hsmall : (epsilon : Real) * R ≤ a)
    (hcontract : (epsilon : Real) *
      (diam (s : Set E) / a) < 1) :
    ∃ q : M, e q ∈ convexHull Real (s : Set E) ∧
      ‖e q - x0‖ ≤ (diam (s : Set E) / a) * ((epsilon : Real) * R) ∧
      ∀ q' : M, e q' ∈ convexHull Real (s : Set E) →
        normalAffineConstraint T (e p) (e q') =
          Tᗮ.orthogonalProjectionOnto
            (e (g (T.orthogonalProjectionOnto (e q' - e p))) - e p -
              (T.orthogonalProjectionOnto (e q' - e p) : E)) → q' = q := by
  have hR : 0 ≤ R := (norm_nonneg (x0 - e p)).trans (hsize x0 hx0)
  have hrho : 0 < rho := lt_of_le_of_lt hR hRrho
  let A0 := normalAffineConstraint T (e p)
  let Q := T.orthogonalProjectionOnto
  let f : T → Tᗮ := fun v => Tᗮ.orthogonalProjectionOnto
    (e (g v) - e p - (v : E))
  have hQ : ‖(Q : E →L[Real] T)‖ ≤ 1 :=
    T.orthogonalProjectionOnto_norm_le
  have hf0 : f 0 = 0 := by
    simp only [f, hg0, sub_self]
    exact Tᗮ.orthogonalProjectionOnto_apply_of_mem_orthogonal (by simp)
  have hfl : LipschitzOnWith epsilon f (ball (0 : T) (2 * rho)) := by
    rw [← hgs]
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro v hv w hw
    have h := hglip.dist_le_mul v hv w hw
    change dist (f v) (f w) ≤ (epsilon : Real) * dist v w
    dsimp only [f]
    calc
      dist (Tᗮ.orthogonalProjectionOnto
          (e (g v) - e p - (v : E)))
          (Tᗮ.orthogonalProjectionOnto
          (e (g w) - e p - (w : E))) ≤
          dist (e (g v) - e p - (v : E))
            (e (g w) - e p - (w : E)) := by
        rw [dist_eq_norm, ← map_sub]
        simpa only [dist_eq_norm] using Tᗮ.norm_orthogonalProjectionOnto_apply_le _
      _ ≤ (epsilon : Real) * dist v w := h
  have hA0 : A0 = normalAffineConstraint T (e p) := rfl
  have hzero : A0 x0 = 0 := by simpa only [A0, hAeq] using hAx0
  have hgap0 : ∀ t : Finset E, t ⊆ s → t.card ≤ Module.finrank Real Tᗮ →
      ∀ x ∈ convexHull Real (t : Set E), a ≤ ‖A0 x‖ := by
    intro t ht htc x hx
    simpa only [A0, hAeq] using hgap t ht htc x hx
  have hr2 : R < 2 * rho := hRrho.trans (by linarith)
  have hsection := exists_unique_lipschitz_graph_section A0 s a ha hcard hgap0 x0 hx0 hzero
    (e p) Q hQ f epsilon (2 * rho) R hsize hr2 hf0 hfl hsmall hcontract
  obtain ⟨x, hx, hxeq, hxerr, huniq⟩ := hsection
  let v : T := Q (x - e p)
  have hvsrc : v ∈ g.source := by
    rw [hgs]
    apply mem_ball_zero_iff.mpr
    have hq : ‖Q (x - e p)‖ ≤ ‖x - e p‖ := by
      calc
        ‖Q (x - e p)‖ ≤ ‖Q‖ * ‖x - e p‖ := Q.le_opNorm _
        _ ≤ ‖x - e p‖ := by simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hQ (norm_nonneg _)
    exact hq.trans_lt ((hsize x hx).trans_lt hr2)
  let q : M := g v
  have hqtarget : q ∈ g.target := g.map_source hvsrc
  have hxe : e q = x := by
    have ht : T.starProjection (x - e p) =
        T.starProjection (e (g v) - e p) := by
      have h := congrArg Subtype.val (hgproj v hvsrc)
      exact h.symm
    have hn : Tᗮ.starProjection (x - e p) =
        Tᗮ.starProjection (e (g v) - e p) := by
      have h : A0 x = f v := by simpa only [A0, hAeq] using hxeq
      change Tᗮ.orthogonalProjectionOnto (x - e p) =
        Tᗮ.orthogonalProjectionOnto
          (e (g v) - e p - (v : E)) at h
      have hz : Tᗮ.orthogonalProjectionOnto (v : E) = 0 :=
        Tᗮ.orthogonalProjectionOnto_apply_of_mem_orthogonal
          (T.le_orthogonal_orthogonal v.property)
      rw [map_sub _ (e (g v) - e p) (v : E), hz, sub_zero] at h
      exact congrArg Subtype.val h
    have hspl (z : E) :
        T.starProjection z + Tᗮ.starProjection z = z :=
      T.starProjection_add_starProjection_orthogonal z
    have hdiff : x - e p = e (g v) - e p := by
      rw [← hspl (x - e p), ← hspl (e (g v) - e p), ht, hn]
    exact (sub_left_injective hdiff).symm
  refine ⟨q, hxe ▸ hx, hxe ▸ hxerr, ?_⟩
  intro q' hq' heq'
  have hqt : q' ∈ g.target := hgcover q' (by
    simpa only [dist_eq_norm] using (hsize (e q') hq').trans_lt hRrho)
  let w : T := g.symm q'
  have hwsrc : w ∈ g.source := g.map_target hqt
  have hwcoord : T.orthogonalProjectionOnto (e q' - e p) = w := by
    rw [← g.right_inv hqt]
    exact hgproj w hwsrc
  have hEq : A (e q') = f (Q (e q' - e p)) := by
    rw [hAeq]
    change Tᗮ.orthogonalProjectionOnto (e q' - e p) =
      Tᗮ.orthogonalProjectionOnto
        (e (g (Q (e q' - e p))) - e p - (Q (e q' - e p) : E))
    have hw : Q (e q' - e p) = w := by
      change T.orthogonalProjectionOnto (e q' - e p) = w
      exact hwcoord
    rw [hw, g.right_inv hqt]
    have hwzero : Tᗮ.orthogonalProjectionOnto (w : E) = 0 :=
      Tᗮ.orthogonalProjectionOnto_apply_of_mem_orthogonal
        (T.le_orthogonal_orthogonal w.property)
    have hleft := Tᗮ.orthogonalProjectionOnto.map_sub (e q') (e p)
    calc
      _ = Tᗮ.orthogonalProjectionOnto (e q') -
          Tᗮ.orthogonalProjectionOnto (e p) := hleft
      _ = Tᗮ.orthogonalProjectionOnto (e q' - e p - (w : E)) := by
        rw [map_sub, hwzero, sub_zero]
        exact hleft.symm
  have hsame : e q' = x := huniq (e q') hq' (by
    simpa only [A0, Q, f, hAeq] using heq')
  exact he (hsame.trans hxe.symm)

end Poincare.Topology
