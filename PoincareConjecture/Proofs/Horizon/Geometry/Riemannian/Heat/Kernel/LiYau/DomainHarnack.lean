import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LiYau.DomainBall
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LiYau.Path
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LiYau.Geodesic

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.LeviCivitaData

set_option backward.isDefEq.respectTransparency false in

theorem exists_heat_harnack_on_domains_containing_ball
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [PreconnectedSpace M] {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (hn : 0 < n) (hcomplete : MetricComplete g)
    {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x), -k * g.inner x v v ≤ D.ricci x v v)
    (O : M) {R : ℝ} (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ Ω : Set M, IsOpen Ω →
      {z | (g.edist O z).toReal ≤ 15 * R} ⊆ Ω →
      ∀ u : ℝ × M → ℝ,
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ u (Ioi 0 ×ˢ Ω) →
        (∀ t, 0 < t → ∀ x ∈ Ω, 0 < u (t, x)) →
        (∀ t, 0 < t → ∀ x ∈ Ω, HasDerivAt (fun s => u (s, x))
          (D.laplacian (fun y => u (t, y)) x) t) →
        ∀ a b : ℝ, 0 < a → a < b → ∀ x y : M,
          (g.edist O x).toReal ≤ R → (g.edist O y).toReal ≤ R →
          u (a, x) ≤ u (b, y) * Real.exp (2 * (n : ℝ) * Real.log (b / a) +
            C * (b - a) + (g.edist x y).toReal ^ 2 / (2 * (b - a))) := by
  obtain ⟨B, hB, hbound⟩ :=
    D.exists_liYau_bound_on_domains_containing_ball hn hcomplete hk hRic O
      (show 1 ≤ 3 * R by linarith)
  refine ⟨B / 2, by positivity, ?_⟩
  intro Ω hΩ hΩball u hu hpos hheat a b ha hab x y hx hy
  have hΩenlarged : {z | (g.edist O z).toReal ≤ 5 * (3 * R)} ⊆ Ω := by
    intro z hz
    apply hΩball
    change (g.edist O z).toReal ≤ 15 * R
    change (g.edist O z).toReal ≤ 5 * (3 * R) at hz
    linarith
  have hxΩ : x ∈ Ω := hΩball (show (g.edist O x).toReal ≤ 15 * R by linarith)
  have hyΩ : y ∈ Ω := hΩball (show (g.edist O y).toReal ≤ 15 * R by linarith)
  obtain ⟨γ, hγ, hγ0, hγ1, hball, hspeed⟩ :=
    g.exists_heat_harnack_path hcomplete O x y hx hy
  have hγΩ : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ Ω := by
    intro s hs
    apply hΩball
    change (g.edist O (γ s)).toReal ≤ 15 * R
    linarith [hball s hs]
  let f := fun p : ℝ × M => Real.log (u p)
  have hf : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ f (Ioi 0 ×ˢ Ω) := by
    intro p hp
    exact (contMDiffAt_log_of_pos
      (hu.contMDiffAt ((isOpen_Ioi.prod hΩ).mem_nhds hp))
      (hpos p.1 hp.1 p.2 hp.2)).contMDiffWithinAt
  have hlog := D.log_harnack_of_gradient_bound_on hΩ hf hγ hγΩ
    (c := 2 * (n : ℝ)) (B := B / 2) (L := (g.edist x y).toReal)
    (fun t ht s hs => ?_) (fun s hs => (hspeed s (Ioo_subset_Icc_self hs)).le) ha hab
  · rw [hγ0, hγ1] at hlog
    have hh : Real.log (u (a, x)) ≤ Real.log (u (b, y)) +
        (2 * (n : ℝ) * Real.log (b / a) + B / 2 * (b - a) +
          (g.edist x y).toReal ^ 2 / (2 * (b - a))) := by
      dsimp [f] at hlog
      linarith
    have he := Real.exp_le_exp.mpr hh
    rwa [Real.exp_add, Real.exp_log (hpos a ha x hxΩ),
      Real.exp_log (hpos b (ha.trans hab) y hyΩ)] at he
  · have hh := hbound Ω hΩ hΩenlarged u hu hpos hheat t ht (γ s) (hball s hs)
    convert hh using 1
    ring

end PoincareConjecture.LeviCivitaData
