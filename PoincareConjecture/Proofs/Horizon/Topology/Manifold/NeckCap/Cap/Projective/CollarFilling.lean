import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Projective.ExteriorBall
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.BallExtension.Collar
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.BallExtension.Center
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Coordinates.Affine












noncomputable section
set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.CapCertificate

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} (C : CapCertificate g)
  (S : StandardPuncturedProjectiveCover M C.puncture C.carrier)



theorem exists_projective_exterior_matching_ball
    (a : UnitThreeSphere) (ha : Quotient.mk' a = C.puncture) :
    let A := connectedComponentIn (C.projectiveClosedCoreLift S)ᶜ a
    ∃ (η σ : ℝ) (b : OpenPartialHomeomorph E3 UnitThreeSphere),
      0 < η ∧ (σ = 1 ∨ σ = -1) ∧
      Metric.closedBall 0 1 ⊆ b.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target ∧
      b 0 = a ∧
      b '' Metric.closedBall 0 1 = closure A ∧
      b '' Metric.ball 0 1 = A ∧ b '' Metric.sphere 0 1 = frontier A ∧
      ∀ (q : UnitTwoSphere) (t : ℝ), |t| < η →
        Real.exp t • (q : E3) ∈ b.source ∧
        Quotient.mk' (b (Real.exp t • (q : E3))) ≠ C.puncture ∧
        S.cover (b (Real.exp t • (q : E3))) =
          C.boundary_neck.coordinate_map (q, σ * t) := by
  let A := connectedComponentIn (C.projectiveClosedCoreLift S)ᶜ a
  obtain ⟨b, hbs, _, hb, hbi, hbcl, hbopen, hbfront⟩ :=
    C.exists_projective_exterior_ball_neighborhood S a ha
  obtain ⟨δ, hδ, e, hes, he, hei, hmem, hfront, hside, σ, hσ, hlift⟩ :=
    C.exists_oriented_projective_exterior_collar S a ha
  let R : Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞ := {
    toEquiv := (Equiv.refl UnitTwoSphere).prodCongr (Equiv.neg ℝ)
    contMDiff_toFun := contMDiff_fst.prodMk contMDiff_snd.neg
    contMDiff_invFun := contMDiff_fst.prodMk contMDiff_snd.neg }
  let c := R.toHomeomorph.toOpenPartialHomeomorph.trans e
  have hcq (z : RoundCylinderSpace) : c z = e (z.1, -z.2) := rfl
  have hzero (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ e.source := by
    rw [hes]
    exact ⟨mem_univ _, neg_lt_zero.mpr hδ, hδ⟩
  have hczero (q : UnitTwoSphere) : c (q, 0) = e (q, 0) := by
    rw [hcq, neg_zero]
  have hc : ContMDiffOn CylModel (𝓡 3) ∞ c c.source :=
    he.comp R.contMDiff.contMDiffOn inter_subset_right
  have hci : ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target :=
    R.symm.contMDiff.comp_contMDiffOn (hei.mono inter_subset_left)
  have hcf : c '' (univ ×ˢ ({0} : Set ℝ)) = b '' Metric.sphere 0 1 := by
    rw [hbfront, hfront]
    ext x
    constructor
    · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
      have ht0 : t = 0 := ht
      subst t
      exact ⟨q, (hczero q).symm⟩
    · rintro ⟨q, rfl⟩
      exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, hczero q⟩
  let j := c.trans b.symm
  let U : Opens RoundCylinderSpace := ⟨j.source, j.open_source⟩
  have hzU (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ U := by
    refine ⟨⟨mem_univ _, ?_⟩, ?_⟩
    · change (q, -(0 : ℝ)) ∈ e.source
      simpa only [neg_zero] using hzero q
    · have hmem := hcf.subset (mem_image_of_mem c
        (show (q, (0 : ℝ)) ∈ univ ×ˢ ({0} : Set ℝ) from ⟨mem_univ _, rfl⟩))
      obtain ⟨x, hx, heq⟩ := hmem
      change c (q, 0) ∈ b.target
      exact heq ▸ b.map_source (hbs (Metric.sphere_subset_closedBall hx))
  obtain ⟨r, hr, hrU⟩ := CylinderGluing.exists_cylinder_collar U hzU
  have hrs : univ ×ˢ Ioo (-r) r ⊆ c.source :=
    fun z hz => (hrU z (abs_lt.mpr hz.2)).1
  have hrt : c '' (univ ×ˢ Ioo (-r) r) ⊆ b.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hrU z (abs_lt.mpr hz.2)).2
  have hpos (q : UnitTwoSphere) (t : ℝ) (ht : 0 < t) (htr : t < r) :
      c (q, t) ∉ b '' Metric.closedBall 0 1 := by
    rw [hbcl, hcq]
    have hzt : (q, t) ∈ c.source := hrs ⟨mem_univ q, by constructor <;> linarith⟩
    have hzs := hzt.2
    change (q, -t) ∈ e.source at hzs
    intro hcl
    have h := (hside _ (e.map_source hzs)).mp hcl
    rw [e.left_inv hzs] at h
    exact (not_le_of_gt ht) (neg_nonneg.mp h)
  obtain ⟨η, d, hη, hηr, hds, _, hd, hdi, hdcl, hmatch⟩ :=
    Poincare.exists_ball_neighborhood_matching_collar b hbs hb hbi c hc hci hr
      hrs hrt hcf hpos
  have hdopen : d '' Metric.ball 0 1 = A := by
    rw [d.image_ball_eq_interior hds (hdcl.trans hbcl),
      ← b.image_ball_eq_interior hbs hbcl]
    exact hbopen
  have haA : a ∈ A := (C.projectiveClosedCoreLift_exterior_components S a ha).2.2.2.2.1
  obtain ⟨ε, k, hε, hks, _, hk, hki, hkcl, hk0, hfix⟩ :=
    Poincare.exists_centered_ball_neighborhood d hds hd hdi (hdopen.symm ▸ haA)
  have hsign : -σ = 1 ∨ -σ = -1 := by rcases hσ with hσ | hσ <;> simp [hσ]
  refine ⟨min η ε, -σ, k, lt_min hη hε, hsign, hks, hk, hki, hk0,
    hkcl.trans (hdcl.trans hbcl), ?_, ?_, ?_⟩
  · rw [k.image_ball_eq_interior hks (hkcl.trans (hdcl.trans hbcl)),
      ← b.image_ball_eq_interior hbs hbcl]
    exact hbopen
  · rw [k.image_sphere_eq_frontier hks (hkcl.trans (hdcl.trans hbcl)),
      ← b.image_sphere_eq_frontier hbs hbcl]
    exact hbfront
  · intro q t ht
    obtain ⟨hsource, hformula⟩ := hmatch (q, t) (lt_of_lt_of_le ht (min_le_left _ _))
    obtain ⟨hsfix, heqfix⟩ := hfix q t (lt_of_lt_of_le ht (min_le_right _ _))
    have hzt : (q, t) ∈ c.source := hrs
      ⟨mem_univ q, abs_lt.mp ((lt_of_lt_of_le ht (min_le_left _ _)).trans hηr)⟩
    have hzs := hzt.2
    change (q, -t) ∈ e.source at hzs
    refine ⟨hsfix.mpr hsource, ?_, ?_⟩
    · rw [heqfix, hformula, hcq]
      exact hmem _ (e.map_source hzs)
    · rw [heqfix, hformula, hcq, hlift _ hzs, mul_neg, neg_mul]



theorem exists_projective_exterior_matching_antipodal_balls
    (a : UnitThreeSphere) (ha : Quotient.mk' a = C.puncture) :
    let K := C.projectiveClosedCoreLift S
    let A := connectedComponentIn Kᶜ a
    ∃ (η σ : ℝ) (b d : OpenPartialHomeomorph E3 UnitThreeSphere),
      0 < η ∧ (σ = 1 ∨ σ = -1) ∧
      Metric.closedBall 0 1 ⊆ b.source ∧
      Metric.closedBall 0 1 ⊆ d.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ d d.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ d.symm d.target ∧
      (∀ x, d x = -b x) ∧
      b 0 = a ∧ d 0 = -a ∧
      b '' Metric.closedBall 0 1 = closure A ∧
      d '' Metric.closedBall 0 1 = closure (Neg.neg '' A) ∧
      b '' Metric.ball 0 1 = A ∧
      d '' Metric.ball 0 1 = Neg.neg '' A ∧
      Disjoint (b '' Metric.closedBall 0 1) (d '' Metric.closedBall 0 1) ∧
      b '' Metric.ball 0 1 ∪ d '' Metric.ball 0 1 = Kᶜ ∧
      b '' Metric.closedBall 0 1 ∪ d '' Metric.closedBall 0 1 = (interior K)ᶜ ∧
      ∀ (q : UnitTwoSphere) (t : ℝ), |t| < η →
        Real.exp t • (q : E3) ∈ b.source ∧
        Real.exp t • (q : E3) ∈ d.source ∧
        Quotient.mk' (b (Real.exp t • (q : E3))) ≠ C.puncture ∧
        Quotient.mk' (d (Real.exp t • (q : E3))) ≠ C.puncture ∧
        S.cover (b (Real.exp t • (q : E3))) =
          C.boundary_neck.coordinate_map (q, σ * t) ∧
        S.cover (d (Real.exp t • (q : E3))) =
          C.boundary_neck.coordinate_map (q, σ * t) := by
  let K := C.projectiveClosedCoreLift S
  let A := connectedComponentIn Kᶜ a
  obtain ⟨η, σ, b, hη, hσ, hbs, hb, hbi, hb0, hbcl, hbopen, _, hmatch⟩ :=
    C.exists_projective_exterior_matching_ball S a ha
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
  let J : Diffeomorph (𝓡 3) (𝓡 3) UnitThreeSphere UnitThreeSphere ∞ := {
    toEquiv := Equiv.neg UnitThreeSphere
    contMDiff_toFun := contMDiff_neg_sphere
    contMDiff_invFun := contMDiff_neg_sphere }
  let d := b.trans J.toHomeomorph.toOpenPartialHomeomorph
  have hds : d.source = b.source := by simp [d]
  have hd : ContMDiffOn (𝓡 3) (𝓡 3) ∞ d d.source :=
    J.contMDiff.comp_contMDiffOn (hb.mono (hds ▸ Subset.rfl))
  have hdi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ d.symm d.target :=
    hbi.comp J.symm.contMDiff.contMDiffOn inter_subset_right
  have hdim (s : Set E3) : d '' s = Neg.neg '' (b '' s) := by
    change (Neg.neg ∘ b) '' s = _
    rw [image_comp]
  have hdcl : d '' Metric.closedBall 0 1 = closure (Neg.neg '' A) := by
    rw [hdim, hbcl]
    exact (Homeomorph.neg UnitThreeSphere).image_closure A
  have hdopen : d '' Metric.ball 0 1 = Neg.neg '' A := by
    rw [hdim, hbopen]
  obtain ⟨_, _, _, hcover, _, _⟩ := C.projectiveClosedCoreLift_exterior_components S a ha
  refine ⟨η, σ, b, d, hη, hσ, hbs, hds.symm ▸ hbs, hb, hbi, hd, hdi,
    fun _ => rfl, hb0, congrArg Neg.neg hb0, hbcl, hdcl, hbopen, hdopen, ?_, ?_, ?_, ?_⟩
  · rw [hbcl, hdcl]
    exact C.disjoint_closure_projectiveClosedCoreLift_exterior S a ha
  · rw [hbopen, hdopen]
    exact hcover
  · rw [hbcl, hdcl, ← closure_union, hcover, closure_compl]
  · intro q t ht
    obtain ⟨hs, hmem, hlift⟩ := hmatch q t ht
    have hneg := (PuncturedProjectiveSphere.antipode
      ⟨b (Real.exp t • (q : E3)), hmem⟩).property
    refine ⟨hs, hds.symm ▸ hs, hmem, hneg, hlift, ?_⟩
    exact ((S.fibers (-b (Real.exp t • (q : E3))) (b (Real.exp t • (q : E3)))
      hneg hmem).mpr (Or.inr rfl)).trans hlift

end PoincareConjecture.CapCertificate
