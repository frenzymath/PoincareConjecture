import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityConeCoordinates
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityUniformCharts











set_option autoImplicit false

open Set Metric MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M65Interior




theorem cone_reconstruction_angular {v d : ℝ → EuclideanSpace ℝ (Fin 3)}
    {v0 : EuclideanSpace ℝ (Fin 3)} {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    {r ρ a b s : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hab : a < b)
    (hv : AbsolutelyContinuousOnInterval v a b)
    (hg : ContDiffOn ℝ 1 g (ball 0 (2 * ρ)))
    (h0 : v0 ∈ closedBall 0 ρ) (hvb : MapsTo v (Icc a b) (closedBall 0 ρ))
    (hd : IntervalIntegrable d volume a b)
    (hinc : ∀ t ∈ Icc a b, ∀ u ∈ Icc a b, v u - v t = ∫ θ in t..u, d θ)
    (hs : s ∈ Icc 0 r) :
    let c := coneCoordinates r v0 v s
    AbsolutelyContinuousOnInterval (g ∘ c) a b ∧
      (∀ᵐ t ∂volume.restrict (Icc a b),
        HasDerivAt (g ∘ c) (fderiv ℝ g (c t) ((s / r) • d t)) t) ∧
      IntervalIntegrable (fun t => fderiv ℝ g (c t) ((s / r) • d t)) volume a b ∧
      ∀ t ∈ Icc a b, ∀ u ∈ Icc a b,
        g (c u) - g (c t) = ∫ θ in t..u, fderiv ℝ g (c θ) ((s / r) • d θ) := by
  let c := coneCoordinates r v0 v s
  have hball : closedBall (0 : EuclideanSpace ℝ (Fin 3)) ρ ⊆ ball 0 (2 * ρ) :=
    closedBall_subset_ball (by linarith)
  obtain ⟨K, hK⟩ := (hg.mono hball).exists_lipschitzOnWith one_ne_zero
    (convex_closedBall _ _) (isCompact_closedBall _ _)
  have hc : MapsTo c (Icc a b) (closedBall 0 ρ) :=
    fun t ht => coneCoordinates_mem_closedBall hr h0 (hvb ht) hs
  have hgD (t : ℝ) (ht : t ∈ Icc a b) : DifferentiableAt ℝ g (c t) :=
    (hg.contDiffAt (isOpen_ball.mem_nhds (hball (hc ht)))).differentiableAt one_ne_zero
  exact ac_chain_integral hab (coneCoordinates_angular_AC hv r v0 s) hK
    (by simpa only [uIcc_of_le hab.le] using hc) hgD (hd.smul (s / r))
    (coneCoordinates_angular_increment hinc r v0 s)

end PoincareConjecture.M65Interior

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {N : ℕ}





theorem m65Cone_embedded_angular (e : M → EuclideanSpace ℝ (Fin N))
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e) (P : EuclideanSpace ℝ (Fin 3) → M)
    {v d : ℝ → EuclideanSpace ℝ (Fin 3)} {v0 : EuclideanSpace ℝ (Fin 3)}
    {r ρ a b s : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hab : a < b)
    (hv : AbsolutelyContinuousOnInterval v a b)
    (hP : ContMDiffOn (𝓡 3) (𝓡 3) 1 P (ball 0 (2 * ρ)))
    (h0 : v0 ∈ closedBall 0 ρ) (hvb : MapsTo v (Icc a b) (closedBall 0 ρ))
    (hd : IntervalIntegrable d volume a b)
    (hinc : ∀ t ∈ Icc a b, ∀ u ∈ Icc a b, v u - v t = ∫ θ in t..u, d θ)
    (hs : s ∈ Icc 0 r) (j : Fin N) :
    let c := M65Interior.coneCoordinates r v0 v s
    let g := fun y => e (P y) j
    AbsolutelyContinuousOnInterval (g ∘ c) a b ∧
      (∀ᵐ t ∂volume.restrict (Icc a b),
        HasDerivAt (g ∘ c) (fderiv ℝ g (c t) ((s / r) • d t)) t) ∧
      IntervalIntegrable (fun t => fderiv ℝ g (c t) ((s / r) • d t)) volume a b ∧
      ∀ t ∈ Icc a b, ∀ u ∈ Icc a b,
        g (c u) - g (c t) = ∫ θ in t..u, fderiv ℝ g (c θ) ((s / r) • d θ) := by
  have hQ : ContDiffOn ℝ 1 (e ∘ P) (ball 0 (2 * ρ)) :=
    contMDiffOn_iff_contDiffOn.mp ((he.of_le (by simp)).comp_contMDiffOn hP)
  have hg : ContDiffOn ℝ 1 (fun y => e (P y) j) (ball 0 (2 * ρ)) :=
    (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ).contDiff.comp_contDiffOn hQ
  exact M65Interior.cone_reconstruction_angular hr hρ hab hv hg h0 hvb hd hinc hs

end PoincareConjecture
