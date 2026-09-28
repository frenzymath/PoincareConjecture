import PoincareConjecture.Proofs.M47.TerminalSourceNormalTransfer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture.M47

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T3Space M]

theorem terminalSourceNormal_edist_eq_on_buffer
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞) (hsource : e.source = univ)
    (hmetric : ∀ x (v w : TangentSpace (𝓡 3) x),
      g.inner x v w = h.inner (e x)
        (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w))
    (p : M) {R : ℝ} (hR : 0 < R)
    (hcover : h.ball (e p) (6 * R) ⊆ e.target)
    {x y : M} (hx : x ∈ g.ball p (2 * R)) (hy : y ∈ g.ball p (2 * R)) :
    g.edist x y = h.edist (e x) (e y) := by
  have hforward := terminalSourceNormal_edist_le g h e hsource hmetric
  apply le_antisymm _ (hforward x y)
  by_contra hnot
  have hxy : h.edist (e x) (e y) < g.edist x y := lt_of_not_ge hnot
  obtain ⟨r, hr, hxr, hry⟩ := ENNReal.lt_iff_exists_real_btwn.mp hxy
  have hxp : g.edist x p < ENNReal.ofReal (2 * R) := by
    have hx' : g.edist p x < ENNReal.ofReal (2 * R) := hx
    simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_comm] using hx'
  have hfour : g.edist x y < ENNReal.ofReal (4 * R) := by
    calc
      _ ≤ g.edist x p + g.edist p y := M36.metric_edist_triangle g x p y
      _ < ENNReal.ofReal (2 * R) + ENNReal.ofReal (2 * R) :=
        ENNReal.add_lt_add hxp hy
      _ = ENNReal.ofReal (4 * R) := by
        rw [← ENNReal.ofReal_add (by positivity : 0 ≤ 2 * R) (by positivity)]
        congr 1
        ring
  have hr4 : r < 4 * R :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < 4 * R)).mp (hry.trans hfour)
  have hsmall : h.ball (e x) r ⊆ e.target := by
    intro z hz
    apply hcover
    calc
      h.edist (e p) z ≤ h.edist (e p) (e x) + h.edist (e x) z :=
        M36.metric_edist_triangle h _ _ _
      _ < ENNReal.ofReal (2 * R) + ENNReal.ofReal r :=
        ENNReal.add_lt_add ((hforward p x).trans_lt hx) hz
      _ = ENNReal.ofReal (2 * R + r) :=
        (ENNReal.ofReal_add (by positivity) hr).symm
      _ ≤ ENNReal.ofReal (6 * R) := ENNReal.ofReal_le_ofReal (by linarith)
  have himage := terminalSourceNormal_ball_image g h e hsource hmetric x r hsmall
  have hyimage : e y ∈ e '' g.ball x r := himage.symm ▸ hxr
  obtain ⟨z, hz, hzy⟩ := hyimage
  have he := e.toOpenPartialHomeomorph.isOpenEmbedding hsource
  have hzy' : z = y := he.injective hzy
  subst z
  exact (not_lt_of_ge hz.le) hry

end PoincareConjecture.M47
