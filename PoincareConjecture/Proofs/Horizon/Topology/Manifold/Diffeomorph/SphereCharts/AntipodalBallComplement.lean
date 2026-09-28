import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.Puncture.BallChartOpening
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.SphereCharts.AntipodalNeighborhood
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.SphereCharts.EquivariantLocalOpening









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric TopologicalSpace
open scoped Manifold ContDiff Topology

namespace Poincare

open PoincareConjecture

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S3" => UnitThreeSphere
local notation "S2" => Metric.sphere (0 : E3) 1




theorem exists_diffeomorph_antipodal_ball_complement
    (b : OpenPartialHomeomorph E3 S3)
    (hbs : closedBall 0 1 ⊆ b.source)
    (hb : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source)
    (hbi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target)
    (hBB : Disjoint (b '' closedBall 0 1) (Neg.neg '' (b '' closedBall 0 1))) :
    ∃ (δ : ℝ) (U V : Opens S3), 0 < δ ∧
      (U : Set S3) = {b 0, -(b 0)}ᶜ ∧
      (V : Set S3) = (b '' closedBall 0 1 ∪ Neg.neg '' (b '' closedBall 0 1))ᶜ ∧
      ∃ (D : Diffeomorph (𝓡 3) (𝓡 3) U V ∞)
        (F : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ positiveHalfLine ∞),
        StrictMono (fun t => (F t : ℝ)) ∧
        (∀ t, δ ≤ t → (F t : ℝ) = t) ∧
        (∀ x y : U, (y : S3) = -(x : S3) → (D y : S3) = -(D x : S3)) ∧
        (∀ (q : S2) (t : ℝ) (x : U), t < 2 * δ →
          (x : S3) = b (Real.exp t • (q : E3)) →
          (D x : S3) = b (Real.exp (F t : ℝ) • (q : E3))) ∧
        (∀ (q : S2) (t : ℝ) (x : U), t < 2 * δ →
          (x : S3) = -b (Real.exp t • (q : E3)) →
          (D x : S3) = -b (Real.exp (F t : ℝ) • (q : E3))) ∧
        ∀ x : U, (x : S3) ∉ b '' closedBall 0 (Real.exp δ) ∪
          Neg.neg '' (b '' closedBall 0 (Real.exp δ)) → (D x : S3) = x := by
  obtain ⟨δ, hδ, hsR, hdisR⟩ :=
    SphereCharts.exists_exponential_antipodal_ball_neighborhood b hbs hBB
  have hδR : Real.exp δ < Real.exp (2 * δ) := Real.exp_lt_exp.mpr (by linarith)
  have h1R : 1 < Real.exp (2 * δ) := (Real.one_lt_exp_iff.mpr hδ).trans hδR
  let O : Opens S3 := ⟨b '' ball 0 (Real.exp (2 * δ)),
    b.isOpen_image_of_subset_source isOpen_ball (ball_subset_closedBall.trans hsR)⟩
  have ha : b 0 ∈ O := mem_image_of_mem b (mem_ball_self (Real.exp_pos _))
  have hB : IsCompact (b '' closedBall 0 1) :=
    (isCompact_closedBall (0 : E3) 1).image_of_continuousOn (b.continuousOn.mono hbs)
  have hBO : b '' closedBall 0 1 ⊆ O := image_mono (closedBall_subset_ball h1R)
  have hK : IsCompact (b '' closedBall 0 (Real.exp δ)) :=
    (isCompact_closedBall (0 : E3) (Real.exp δ)).image_of_continuousOn
      (b.continuousOn.mono ((closedBall_subset_closedBall hδR.le).trans hsR))
  have hKO : b '' closedBall 0 (Real.exp δ) ⊆ O :=
    image_mono (closedBall_subset_ball hδR)
  have hdis : Disjoint (O : Set S3) (Neg.neg '' (O : Set S3)) :=
    hdisR.mono (image_mono ball_subset_closedBall)
      (image_mono (image_mono ball_subset_closedBall))
  obtain ⟨e, hes, het, he, hei, hfix, hifix, F, hmono, hFfix, hradial⟩ :=
    exists_ball_chart_opening b hb hbi hδ hδR hsR
  obtain ⟨U, V, hU, hV, D, hD, hDi, hneg, hfixed⟩ :=
    exists_equivariant_diffeomorph_of_local_opening O (b 0) ha hB hBO hK hKO hdis
      e hes het he hei hfix hifix
  have hrad (q : S2) (t : ℝ) (x : U) (ht : t < 2 * δ)
      (hx : (x : S3) = b (Real.exp t • (q : E3))) :
      (D x : S3) = b (Real.exp (F t : ℝ) • (q : E3)) := by
    have htR : Real.exp t < Real.exp (2 * δ) := Real.exp_lt_exp.mpr ht
    have hxO : (x : S3) ∈ O := by
      rw [hx]
      apply mem_image_of_mem
      simpa only [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos t), norm_eq_of_mem_sphere q, mul_one] using htR
    rw [hD, if_pos hxO, hx]
    exact hradial q t htR
  refine ⟨δ, U, V, hδ, hU, hV, D, F, hmono, hFfix, hneg, hrad, ?_, hfixed⟩
  intro q t x ht hx
  have hnx : -(x : S3) ∈ U := by
    have hxp : (x : S3) ∉ {b 0, -(b 0)} := hU.subset x.property
    apply hU.superset
    simpa only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, neg_eq_iff_eq_neg,
      neg_neg, or_comm] using hxp
  let y : U := ⟨-(x : S3), hnx⟩
  have hy : (y : S3) = b (Real.exp t • (q : E3)) := by
    dsimp [y]
    rw [hx, neg_neg]
  have hneg' := hneg x y rfl
  rw [hrad q t y ht hy] at hneg'
  simpa only [neg_neg] using (congrArg Neg.neg hneg').symm

end Poincare
