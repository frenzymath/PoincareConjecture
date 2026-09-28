import PoincareConjecture.Proofs.M10.IntrinsicLipschitz
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Volume.Surgery.Measure.Distance.PathSupports

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal NNReal

universe u

namespace PoincareConjecture.SurgeryVolume.Measure

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in

theorem edist_le_mul_riemannianEDist_of_upper_supports
    (g : RiemannianMetric n M) {f : M → ℝ} {U : Set M}
    (hf : ContinuousOn f U) {C : ℝ≥0}
    (hsupport : ∀ q ∈ U, ∃ B : M → ℝ,
      MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) B q ∧ B q = f q ∧
        (∀ᶠ x in 𝓝 q, f x ≤ B x) ∧ ∀ v : TangentSpace (𝓡 n) q,
          |mvfderiv (𝓡 n) B q v| ≤ C * g.tangentNorm q v)
    {x₀ x y : M} {r : ℝ≥0}
    (hball : ∀ q, g.edist x₀ q < (r : ℝ≥0∞) + r + r → q ∈ U)
    (hx : g.edist x₀ x < r) (hy : g.edist x₀ y < r) :
    edist (f x) (f y) ≤ (C : ℝ≥0∞) * g.edist x y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hd : g.edist x y < (r : ℝ≥0∞) + r := by
    calc
      g.edist x y ≤ g.edist x x₀ + g.edist x₀ y :=
        Manifold.riemannianEDist_triangle
      _ < (r : ℝ≥0∞) + r := ENNReal.add_lt_add
        (by simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_comm] using hx) hy
  let : (𝓝[>] (g.edist x y)).NeBot := nhdsGT_neBot_of_exists_gt ⟨_, hd⟩
  have hlim : Tendsto (fun R : ℝ≥0∞ ↦ (C : ℝ≥0∞) * R)
      (𝓝[>] (g.edist x y)) (𝓝 ((C : ℝ≥0∞) * g.edist x y)) :=
    (ENNReal.continuous_const_mul ENNReal.coe_ne_top).continuousWithinAt
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (eventually_lt_nhds hd)] with R hR hRsmall
  obtain ⟨γ, hγx, hγy, hγ, hlength, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt
      (I := 𝓡 n) hR zero_lt_one
  have hγU : MapsTo γ (Icc 0 1) U := by
    intro t ht
    apply hball
    have hprefix : g.edist x (γ t) ≤ g.pathELength γ 0 1 :=
      (Manifold.riemannianEDist_le_pathELength hγ.contMDiffOn hγx rfl ht.1).trans
        (Manifold.pathELength_mono le_rfl ht.2)
    calc
      g.edist x₀ (γ t) ≤ g.edist x₀ x + g.edist x (γ t) :=
        Manifold.riemannianEDist_triangle
      _ ≤ g.edist x₀ x + g.pathELength γ 0 1 := add_le_add_right hprefix _
      _ < (r : ℝ≥0∞) + (r + r) :=
        ENNReal.add_lt_add hx (hlength.trans hRsmall)
      _ = (r : ℝ≥0∞) + r + r := (add_assoc _ _ _).symm
  have hpath := edist_le_pathELength_of_upper_supports g hf C.coe_nonneg hsupport hγ hγU
  simp only [hγx, hγy, ENNReal.ofReal_coe_nnreal] at hpath
  exact hpath.trans (mul_le_mul_right hlength.le _)

end PoincareConjecture.SurgeryVolume.Measure
