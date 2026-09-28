import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.Projective.BallComplement
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.SphereCharts.AntipodalBallComplement

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric TopologicalSpace Filter Classical
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.ProjectiveGluing

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S3" => UnitThreeSphere

section Transport

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
  {p : RealProjectiveThree} {A : Set M}
  (S : StandardPuncturedProjectiveCover M p A)

theorem exists_cover_of_equivariant_domain_diffeomorph
    (U V : Opens S3) (hU : (U : Set S3) = {x : S3 | Quotient.mk' x ≠ p})
    (hV : (V : Set S3) ⊆ {x : S3 | Quotient.mk' x ≠ p})
    (D : Diffeomorph (𝓡 3) (𝓡 3) U V ∞)
    (hneg : ∀ x y : U, (y : S3) = -(x : S3) → (D y : S3) = -(D x : S3)) :
    ∃ T : StandardPuncturedProjectiveCover M p (S.cover '' (V : Set S3)),
      ∀ x : U, T.cover x = S.cover (D x) := by
  let f : S3 → M := fun x => if hx : x ∈ U then S.cover (D ⟨x, hx⟩) else S.cover x
  have hf (x : U) : f x = S.cover (D x) := dif_pos x.property
  have himage : f '' {x : S3 | Quotient.mk' x ≠ p} = S.cover '' (V : Set S3) := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      let y : U := ⟨x, hU.superset hx⟩
      rw [hf y]
      exact mem_image_of_mem S.cover (D y).property
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy⟩ := D.surjective (⟨x, hx⟩ : V)
      refine ⟨y, hU.subset y.property, ?_⟩
      rw [hf]
      exact congrArg S.cover (congrArg Subtype.val hy)
  have hanti (x : U) : -(x : S3) ∈ U := by
    apply hU.superset
    exact (PuncturedProjectiveSphere.antipode ⟨x, hU.subset x.property⟩).property
  have hfibers (x y : S3) (hx : Quotient.mk' x ≠ p) (hy : Quotient.mk' y ≠ p) :
      f x = f y ↔ x = y ∨ x = -y := by
    let X : U := ⟨x, hU.superset hx⟩
    let Y : U := ⟨y, hU.superset hy⟩
    let Yneg : U := ⟨-y, hanti Y⟩
    have hDY : (D Yneg : S3) = -(D Y : S3) := hneg Y Yneg rfl
    rw [hf X, hf Y, S.fibers _ _ (hV (D X).property) (hV (D Y).property)]
    constructor
    · rintro (h | h)
      · exact Or.inl (congrArg Subtype.val (D.injective (Subtype.ext h)))
      · right
        exact congrArg Subtype.val (D.injective (Subtype.ext (h.trans hDY.symm)))
    · rintro (h | h)
      · exact Or.inl (congrArg (fun z : U => (D z : S3)) (Subtype.ext h))
      · right
        exact (congrArg (fun z : U => (D z : S3)) (show X = Yneg from Subtype.ext h)).trans hDY
  have hlocalU : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) := by
    intro x
    have hDv := (D.isLocalDiffeomorph x).comp (𝓡 3) S3
      (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) V (D x))
    have hcomp := hDv.comp (𝓡 3) M (S.local_diffeomorph ⟨D x, hV (D x).property⟩)
    exact hcomp.congr_of_eventuallyEq (Eventually.of_forall hf)
  have hlocal : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ f
      {x : S3 | Quotient.mk' x ≠ p} := by
    intro x
    let y : U := ⟨x, hU.superset x.property⟩
    exact (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) U y).of_comp (hlocalU y)
  exact ⟨⟨f, himage, hfibers, hlocal⟩, hf⟩

end Transport

section BallComplement

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]
  {p : RealProjectiveThree} {A : Set M}
  (S : StandardPuncturedProjectiveCover M p A)

theorem exists_punctured_cover_ball_complement
    (a : S3) (ha : Quotient.mk' a = p)
    (b : OpenPartialHomeomorph E3 S3)
    (hbs : closedBall 0 1 ⊆ b.source)
    (hb : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source)
    (hbi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target)
    (hb0 : b 0 = a)
    (hBB : Disjoint (b '' closedBall 0 1) (Neg.neg '' (b '' closedBall 0 1))) :
    ∃ (δ : ℝ) (F : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ Poincare.positiveHalfLine ∞)
      (T : StandardPuncturedProjectiveCover M p
        (interior (S.cover '' antipodalBallComplement b))),
      0 < δ ∧ StrictMono (fun t => (F t : ℝ)) ∧
      (∀ t, δ ≤ t → (F t : ℝ) = t) ∧
      (∀ (q : UnitTwoSphere) (t : ℝ), t ≤ 0 →
        T.cover (b (Real.exp t • (q : E3))) = S.cover (b (Real.exp (F t : ℝ) • (q : E3)))) ∧
      (∀ (q : UnitTwoSphere) (t : ℝ), t ≤ 0 →
        T.cover (-b (Real.exp t • (q : E3))) = S.cover (-b (Real.exp (F t : ℝ) • (q : E3)))) ∧
      ∀ x : S3, Quotient.mk' x ≠ p →
        x ∉ b '' closedBall 0 (Real.exp δ) ∪ Neg.neg '' (b '' closedBall 0 (Real.exp δ)) →
        T.cover x = S.cover x := by
  obtain ⟨δ, U, V, hδ, hU, hV, D, F, hmono, hFfix, hneg, hrad, hnrad, hfixed⟩ :=
    Poincare.exists_diffeomorph_antipodal_ball_complement b hbs hb hbi hBB
  have hpairs : {x : S3 | Quotient.mk' x ≠ p} = {b 0, -(b 0)}ᶜ := by
    rw [hb0, ← ha]
    ext x
    exact not_congr Quotient.eq
  have hVp : (V : Set S3) ⊆ {x : S3 | Quotient.mk' x ≠ p} := by
    intro x hx
    apply antipodalBallComplement_avoids_puncture a ha b hb0
    exact (compl_subset_compl.mpr
      (union_subset_union (image_mono ball_subset_closedBall)
        (image_mono (image_mono ball_subset_closedBall)))) (hV.subset hx)
  obtain ⟨T, hT⟩ := exists_cover_of_equivariant_domain_diffeomorph S U V
    (hU.trans hpairs.symm) hVp D hneg
  have hi : interior (S.cover '' antipodalBallComplement b) = S.cover '' (V : Set S3) := by
    rw [hV]
    exact (projectiveBallComplement_topology S a ha b hbs hb0 hBB).2.1
  let T' : StandardPuncturedProjectiveCover M p
      (interior (S.cover '' antipodalBallComplement b)) :=
    { T with image_eq := T.image_eq.trans hi.symm }
  have hpoint (q : UnitTwoSphere) (t : ℝ) (ht : t ≤ 0) :
      b (Real.exp t • (q : E3)) ∈ U := by
    have hxball : Real.exp t • (q : E3) ∈ closedBall (0 : E3) 1 := by
      simp only [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos t), norm_eq_of_mem_sphere q, mul_one]
      exact Real.exp_le_one_iff.mpr ht
    have hbball : b (Real.exp t • (q : E3)) ∈ b '' closedBall (0 : E3) 1 :=
      mem_image_of_mem b hxball
    apply hU.superset
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    refine ⟨?_, ?_⟩
    · intro h
      exact smul_ne_zero (Real.exp_ne_zero _) (ne_zero_of_mem_unit_sphere q)
        (b.injOn (hbs hxball) (hbs (by simp)) h)
    · intro h
      exact disjoint_left.mp hBB hbball
        ⟨b 0, mem_image_of_mem b (by simp), h.symm⟩
  have hnpoint (q : UnitTwoSphere) (t : ℝ) (ht : t ≤ 0) :
      -b (Real.exp t • (q : E3)) ∈ U := by
    apply (hU.trans hpairs.symm).superset
    exact (PuncturedProjectiveSphere.antipode
      ⟨_, (hU.trans hpairs.symm).subset (hpoint q t ht)⟩).property
  refine ⟨δ, F, T', hδ, hmono, hFfix, ?_, ?_, ?_⟩
  · intro q t ht
    let x : U := ⟨b (Real.exp t • (q : E3)), hpoint q t ht⟩
    change T.cover x = _
    rw [hT x, hrad q t x (by linarith) rfl]
  · intro q t ht
    let x : U := ⟨-b (Real.exp t • (q : E3)), hnpoint q t ht⟩
    change T.cover x = _
    rw [hT x, hnrad q t x (by linarith) rfl]
  · intro x hx hxK
    let y : U := ⟨x, (hU.trans hpairs.symm).superset hx⟩
    change T.cover y = _
    rw [hT y, hfixed y hxK]

end BallComplement

end PoincareConjecture.ProjectiveGluing
