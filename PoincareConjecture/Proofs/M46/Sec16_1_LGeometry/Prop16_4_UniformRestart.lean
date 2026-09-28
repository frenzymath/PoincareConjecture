import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_4_UniformSliceImage
import PoincareConjecture.Proofs.M14.Sec6_3_ClosedEulerRestart










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.Proofs.M46

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]




theorem closedODE_exists_uniform_restart_neighborhood
    {a b : ℝ} (hab : a < b) (t₀ : Icc a b)
    {U : Set E} (hU : IsOpen U) (f : ℝ × E → E)
    (hf : ContDiffOn ℝ ∞ f (Icc a b ×ˢ U)) {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ c d : ℝ, c < d ∧ a ≤ c ∧ d ≤ b ∧ Icc c d ∈ 𝓝[Icc a b] t₀.val ∧
      ∃ R : ℝ, 0 < R ∧ ∀ᶠ r in 𝓝[Icc a b] t₀.val,
        r ∈ Icc c d ∧ ∀ y ∈ ball x₀ R, ∃ gamma : ℝ → E,
          gamma r = y ∧ ContDiffOn ℝ ∞ gamma (Icc c d) ∧
          ∀ s ∈ Icc c d, gamma s ∈ U ∧
            HasDerivWithinAt gamma (f (s, gamma s)) (Icc c d) s := by
  obtain ⟨c, d, t₁, hcd, hac, hdb, hi, hnear, rho, hrho, alpha, halpha, hdata⟩ :=
    M14.closedODE_exists_joint_family hab t₀ hU f hf hx₀
  have hx : x₀ ∈ ball x₀ rho := mem_ball_self hrho
  have ht : t₀.val ∈ Icc c d := hi ▸ t₁.property
  have hinit (x : E) (hx' : x ∈ ball x₀ rho) : alpha (x, t₀.val) = x :=
    hi ▸ (hdata x hx').1
  obtain ⟨R, hR, hsurj⟩ := closedFamily_exists_uniform_image_ball
    (uniqueDiffOn_Icc hcd) isOpen_ball alpha halpha hx ht hinit
  have hfilter : 𝓝[Icc a b] t₀.val ≤ 𝓝[Icc c d] t₀.val :=
    le_inf nhdsWithin_le_nhds (le_principal_iff.mpr hnear)
  refine ⟨c, d, hcd, hac, hdb, hnear, R, hR, ?_⟩
  filter_upwards [hsurj.filter_mono hfilter, hnear] with r hr hrC
  refine ⟨hrC, ?_⟩
  intro y hy
  obtain ⟨z, hz, heq⟩ := hr hy
  refine ⟨fun s => alpha (z, s), heq, ?_, (hdata z hz).2⟩
  exact halpha.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hs => ⟨hz, hs⟩)

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]





theorem exists_closedChartEulerPhase_uniform_restart_neighborhood
    {J : Set ℝ} (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T : ℝ) (x₀ : M) {a b : ℝ} (hab : a < b)
    (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ J) (s₀ : Icc a b)
    {z₀ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)}
    (hcenter : z₀.1 ∈ (extChartAt (𝓡 n) x₀).target) :
    ∃ c d : ℝ, c < d ∧ a ≤ c ∧ d ≤ b ∧ Icc c d ∈ 𝓝[Icc a b] s₀.val ∧
      ∃ R : ℝ, 0 < R ∧ ∀ᶠ r in 𝓝[Icc a b] s₀.val,
        r ∈ Icc c d ∧ ∀ z ∈ ball z₀ R,
          ∃ gamma : ℝ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
            gamma r = z ∧ ContDiffOn ℝ ∞ gamma (Icc c d) ∧
            ∀ s ∈ Icc c d,
              (gamma s).1 ∈ (extChartAt (𝓡 n) x₀).target ∧
                HasDerivWithinAt gamma
                  (M08.closedChartEulerPhase F T x₀ (Icc c d) s (gamma s))
                  (Icc c d) s := by
  obtain ⟨c, d, hcd, hac, hdb, hnear, R, hR, hrestart⟩ :=
    closedODE_exists_uniform_restart_neighborhood hab s₀
      ((isOpen_extChartAt_target (I := 𝓡 n) x₀).prod isOpen_univ)
      (Function.uncurry (M08.closedChartEulerPhase F T x₀ (Icc a b)))
      (M08.closedChartEulerPhase_contDiffOn F hM04 T x₀ (uniqueDiffOn_Icc hab) htime)
      ⟨hcenter, mem_univ _⟩
  refine ⟨c, d, hcd, hac, hdb, hnear, R, hR, ?_⟩
  filter_upwards [hrestart] with r hr
  refine ⟨hr.1, ?_⟩
  intro z hz
  obtain ⟨gamma, hgamma, hsmooth, hdata⟩ := hr.2 z hz
  refine ⟨gamma, hgamma, hsmooth, ?_⟩
  intro s hs
  obtain ⟨hmap, hd⟩ := hdata s hs
  refine ⟨hmap.1, ?_⟩
  rw [M14.closedChartEulerPhase_restrict F hM04 T x₀ htime
    (Icc_subset_Icc hac hdb) hs hmap.1]
  exact hd

end PoincareConjecture.Proofs.M46
