import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.LocalIsometry.Round
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.LocalIsometry.SphereMotions


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter PoincareConjecture
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.Geometry.Riemannian.SpaceForm

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]


theorem inverse_local_isometry_inner
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (F : OpenPartialHomeomorph M N)
    (hF : ContMDiffOn (𝓡 n) (𝓡 n) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 n) (𝓡 n) ∞ F.symm F.target)
    (hm : ∀ x ∈ F.source, ∀ v w : TangentSpace (𝓡 n) x,
      g.inner x v w = h.inner (F x)
        (mfderiv (𝓡 n) (𝓡 n) F x v) (mfderiv (𝓡 n) (𝓡 n) F x w))
    (y : N) (hy : y ∈ F.target) (v w : TangentSpace (𝓡 n) y) :
    h.inner y v w = g.inner (F.symm y)
      (mfderiv (𝓡 n) (𝓡 n) F.symm y v)
      (mfderiv (𝓡 n) (𝓡 n) F.symm y w) := by
  have hd : F.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨hF.mdifferentiableOn (by simp), hFi.mdifferentiableOn (by simp)⟩
  have hid (u : TangentSpace (𝓡 n) y) :
      mfderiv (𝓡 n) (𝓡 n) F (F.symm y)
        (mfderiv (𝓡 n) (𝓡 n) F.symm y u) = u :=
    congrArg (fun L => L u) (hd.comp_symm_deriv hy)
  have hi := hm (F.symm y) (F.map_target hy)
    (mfderiv (𝓡 n) (𝓡 n) F.symm y v)
    (mfderiv (𝓡 n) (𝓡 n) F.symm y w)
  erw [F.right_inv hy] at hi
  exact (hi.trans (congrArg₂ (fun (a b : TangentSpace (𝓡 n) y) => h.inner y a b)
    (hid v) (hid w))).symm


theorem exists_uniform_round_chart_radius [T2Space M] [CompactSpace M]
    (g : RiemannianMetric n M)
    (hsec : ∀ (x : M) (u v : TangentSpace (𝓡 n) x),
      g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 ≠ 0 →
        g.leviCivitaData.sectionalCurvature x u v = 1)
    (q : UnitSphere n) :
    ∃ r : ℝ, 0 < r ∧ ∀ p : M, ∃ F : OpenPartialHomeomorph M (UnitSphere n),
      p ∈ F.source ∧ Metric.ball (F p) r ⊆ F.target ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ F F.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ F.symm F.target ∧
      ∀ x ∈ F.source, ∀ v w : TangentSpace (𝓡 n) x,
        g.inner x v w = (roundSphereMetric n).inner (F x)
          (mfderiv (𝓡 n) (𝓡 n) F x v) (mfderiv (𝓡 n) (𝓡 n) F x w) := by
  classical
  rcases isEmpty_or_nonempty M with hM | hM
  · exact ⟨1, zero_lt_one, fun p => (hM.false p).elim⟩
  let p₀ : M := Classical.choice hM
  choose F hp _ hF hFi hm using fun p : M => exists_local_isometry_unitSphere g hsec p q
  have hball (p : M) : ∃ ε : ℝ, 0 < ε ∧ Metric.ball (F p p) (2 * ε) ⊆ (F p).target := by
    obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp
      ((F p).open_target.mem_nhds ((F p).map_source (hp p)))
    refine ⟨δ / 2, half_pos hδ, ?_⟩
    simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hsub
  choose ε hε hεball using hball
  let V (p : M) := (F p).source ∩ F p ⁻¹' Metric.ball (F p p) (ε p)
  have hV (p : M) : IsOpen (V p) := (F p).isOpen_inter_preimage Metric.isOpen_ball
  have hpV (p : M) : p ∈ V p := ⟨hp p, Metric.mem_ball_self (hε p)⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover V hV
    (fun p _ => mem_iUnion.mpr ⟨p, hpV p⟩)
  have hsne : s.Nonempty := by
    obtain ⟨p, hp, _⟩ := mem_iUnion₂.mp (hs (mem_univ p₀))
    exact ⟨p, hp⟩
  refine ⟨s.inf' hsne ε, (Finset.lt_inf'_iff hsne).mpr (fun p _ => hε p), ?_⟩
  intro p
  obtain ⟨a, ha, hpa⟩ := mem_iUnion₂.mp (hs (mem_univ p))
  refine ⟨F a, hpa.1, ?_, hF a, hFi a, hm a⟩
  intro z hz
  apply hεball a
  rw [Metric.mem_ball] at hz ⊢
  have hnear : dist (F a p) (F a a) < ε a := hpa.2
  have hr : s.inf' hsne ε ≤ ε a := Finset.inf'_le ε ha
  exact (dist_triangle z (F a p) (F a a)).trans_lt (by linarith)

theorem isometry_sphereMotion
    (L : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1))) :
    Isometry (sphereMotion L) := by
  intro x y
  change edist (L (x : EuclideanSpace ℝ (Fin (n + 1))))
    (L (y : EuclideanSpace ℝ (Fin (n + 1)))) = edist _ _
  exact L.isometry.edist_eq _ _

end Poincare.Geometry.Riemannian.SpaceForm
