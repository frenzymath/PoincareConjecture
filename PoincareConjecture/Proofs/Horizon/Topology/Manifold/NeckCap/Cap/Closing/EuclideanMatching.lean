import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.EuclideanComplement
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.BallExtension.Collar

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem exists_two_cap_euclidean_matching_balls (C D : CapCertificate g)
    (hC : C.model_kind = .euclidean) (hD : D.model_kind = .euclidean)
    (hcompact : IsCompact (C.carrier ∪ D.carrier)) :
    ∃ (r : ℝ) (b₀ b₁ : OpenPartialHomeomorph E3 M),
      0 < r ∧ b₀.source = univ ∧ b₀.target = D.carrier ∧ b₁.target ⊆ C.carrier ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b₀ b₀.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b₀.symm b₀.target ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b₁ b₁.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b₁.symm b₁.target ∧
      Metric.ball 0 (Real.exp r) ⊆ b₀.source ∧
      Metric.ball 0 (Real.exp r) ⊆ b₁.source ∧
      b₀.target ⊆ C.carrier ∪ D.carrier ∧ b₁.target ⊆ C.carrier ∪ D.carrier ∧
      b₁ '' Metric.closedBall 0 1 = (C.carrier ∪ D.carrier) \ b₀ '' Metric.ball 0 1 ∧
      b₀ '' Metric.closedBall 0 1 ∪ b₁ '' Metric.closedBall 0 1 = C.carrier ∪ D.carrier ∧
      b₀ '' Metric.closedBall 0 1 ∩ b₁ '' Metric.closedBall 0 1 = b₀ '' Metric.sphere 0 1 ∧
      ∀ (q : UnitTwoSphere) (t : ℝ), |t| < r →
        b₀ (Real.exp t • (q : E3)) = b₁ (Real.exp (-t) • (q : E3)) := by
  obtain ⟨b, d, hbs, hbt, hb, hbi, hds, hdt, hd, hdi, hdclosed, _, hdsphere,
    hcover, hinter, c, hcs, hc, hci, hformula, hzero, δ, hδ, htarget, hnegative, _⟩ :=
    C.exists_two_cap_euclidean_complementary_balls D hC hD hcompact
  let R : Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞ := {
    toEquiv := (Equiv.refl UnitTwoSphere).prodCongr (Equiv.neg ℝ)
    contMDiff_toFun := contMDiff_fst.prodMk contMDiff_snd.neg
    contMDiff_invFun := contMDiff_fst.prodMk contMDiff_snd.neg }
  let e := R.toHomeomorph.toOpenPartialHomeomorph.trans c
  have hes : e.source = univ := by simp [e, hcs]
  have heq (p : RoundCylinderSpace) : e p = c (p.1, -p.2) := rfl
  have he : ContMDiffOn CylModel (𝓡 3) ∞ e e.source :=
    hc.comp R.contMDiff.contMDiffOn inter_subset_right
  have hei : ContMDiffOn (𝓡 3) CylModel ∞ e.symm e.target :=
    R.symm.contMDiff.comp_contMDiffOn (hci.mono inter_subset_left)
  have hsource : univ ×ˢ Ioo (-δ) δ ⊆ e.source := by rw [hes]; exact subset_univ _
  have hetarget : e '' (univ ×ˢ Ioo (-δ) δ) ⊆ d.target := by
    rintro _ ⟨p, hp, rfl⟩
    rw [heq]
    exact (htarget ⟨(p.1, -p.2), ⟨mem_univ _, by constructor <;> linarith [hp.2.1, hp.2.2]⟩,
      rfl⟩).2
  have hezero : e '' (univ ×ˢ ({0} : Set ℝ)) = d '' Metric.sphere 0 1 := by
    rw [hdsphere, ← hzero]
    ext x
    constructor
    · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
      have ht0 : t = 0 := ht
      subst t
      exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, by simp [heq]⟩
    · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
      have ht0 : t = 0 := ht
      subst t
      exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, by simp [heq]⟩
  have hepositive (q : UnitTwoSphere) (t : ℝ) (ht : 0 < t) (htδ : t < δ) :
      e (q, t) ∉ d '' Metric.closedBall 0 1 := by
    rw [hdclosed]
    intro hmem
    apply hmem.2
    rw [heq]
    exact hnegative ⟨(q, -t), ⟨mem_univ _, by constructor <;> linarith⟩, rfl⟩
  obtain ⟨r, a, hr, _, has, hat, ha, hai, haclosed, hmatch⟩ :=
    Poincare.exists_ball_neighborhood_matching_collar d hds hd hdi e he hei hδ
      hsource hetarget hezero hepositive
  have haball : Metric.ball (0 : E3) (Real.exp r) ⊆ a.source := by
    intro x hx
    by_cases hle : ‖x‖ ≤ 1
    · exact has (by simpa using hle)
    · have hx1 : 1 < ‖x‖ := lt_of_not_ge hle
      have hx0 : x ≠ 0 := by intro h; norm_num [h] at hx1
      let J := Poincare.sphereCylinderDiffeomorphPunctured
      let p := J.symm ⟨x, hx0⟩
      have hp : Real.exp p.2 • (p.1 : E3) = x :=
        congrArg Subtype.val (J.apply_symm_apply ⟨x, hx0⟩)
      have hnorm : Real.exp p.2 = ‖x‖ := by
        rw [← hp, norm_smul]
        simp [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have hp0 : 0 < p.2 := Real.exp_lt_exp.mp (by simpa only [Real.exp_zero, hnorm] using hx1)
      have hpr : p.2 < r := Real.exp_lt_exp.mp (by simpa only [hnorm, mem_ball_zero_iff] using hx)
      exact hp ▸ (hmatch p (by simpa only [abs_of_pos hp0] using hpr)).1
  refine ⟨r, b, a, hr, hbs, hbt, hat ▸ hdt, hb, hbi, ha, hai,
    hbs.symm ▸ subset_univ _, haball, hbt.symm ▸ subset_union_right,
    (hat ▸ hdt).trans subset_union_left, haclosed.trans hdclosed, ?_, ?_, ?_⟩
  · rw [haclosed]
    exact hcover
  · rw [haclosed]
    exact hinter
  · intro q t ht
    have hm := (hmatch (q, -t) (by simpa only [abs_neg] using ht)).2
    simpa only [heq, neg_neg, hformula] using hm.symm

end PoincareConjecture.CapCertificate
