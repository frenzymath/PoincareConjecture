import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarCoverInjective

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)

theorem exists_injective_local_annular_conjugate {H : Plane → ℝ} {V : Cover → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hdV : ∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z)
    {P : ℝ} (hP : P ≠ 0)
    (hinj : InjOn (scalarNormalizedCoverMap H V P) scalarCoverStrip)
    {z : Cover} (hz : z ∈ scalarCoverStrip) :
    ∃ (U : Set Plane) (W : Plane → ℝ), IsOpen U ∧ scalarCoverMap z ∈ U ∧
      U ⊆ scalarAnnulus ∧ ContDiff ℝ ∞ W ∧
      (∀ x ∈ U, HasFDerivAt W (scalarConjugateForm D H x) x) ∧
      InjOn (scalarConjugatePair H W) U := by
  obtain ⟨r, W, hr, hAnn, hWs, hdW⟩ :=
    exists_local_annular_conjugate D hHs hlap (scalarCoverMap_mem hz)
  obtain ⟨s, hs, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem
    (scalarCoverStrip_isOpen.mem_nhds hz)
    (scalarCoverMap_smooth.continuous.continuousAt.preimage_mem_nhds
      (Metric.ball_mem_nhds (scalarCoverMap z) hr)))
  let Q : Cover → ℝ := fun y => V y - W (scalarCoverMap y)
  have hQ (y : Cover) (hy : y ∈ Metric.ball z s) :
      HasFDerivAt Q (0 : Cover →L[ℝ] ℝ) y := by
    have h := (hdV y (hball hy).1).sub ((hdW _ (hball hy).2).comp y
      (scalarCoverMap_smooth.differentiable (by simp) y).hasFDerivAt)
    simpa only [Q, Function.comp_def, scalarCoverForm, sub_self] using! h
  obtain ⟨c, hc⟩ := Metric.isOpen_ball.exists_is_const_of_fderiv_eq_zero
    (convex_ball z s).isPreconnected
    (fun y hy => (hQ y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => (hQ y hy).fderiv)
  let T := scalarConjugateNormalization P c hP
  have heq (y : Cover) (hy : y ∈ Metric.ball z s) :
      scalarNormalizedCoverMap H V P y = T (scalarConjugatePair H W (scalarCoverMap y)) := by
    have hyc : V y - W (scalarCoverMap y) = c := hc y hy
    have hv : V y = W (scalarCoverMap y) + c := by linarith
    ext <;> simp [scalarNormalizedCoverMap, T, scalarConjugateNormalization,
      scalarConjugatePair, hv]
  have himage : scalarCoverMap '' Metric.ball z s ∈ 𝓝 (scalarCoverMap z) := by
    rw [← scalarCoverMap_map_nhds (ne_of_gt (lt_trans zero_lt_one hz.1))]
    exact Filter.image_mem_map (Metric.ball_mem_nhds z hs)
  obtain ⟨U, hUsub, hUo, hpU⟩ := mem_nhds_iff.mp himage
  have hUball : U ⊆ Metric.ball (scalarCoverMap z) r := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hUsub hx
    exact (hball hy).2
  refine ⟨U, W, hUo, hpU, hUball.trans hAnn, hWs,
    fun x hx => hdW x (hUball hx), ?_⟩
  intro x hx y hy hpair
  obtain ⟨a, ha, rfl⟩ := hUsub hx
  obtain ⟨b, hb, rfl⟩ := hUsub hy
  have hab : a = b := hinj (hball ha).1 (hball hb).1 (by rw [heq a ha, heq b hb, hpair])
  exact congrArg scalarCoverMap hab

end PoincareConjecture.M64Uniformization
