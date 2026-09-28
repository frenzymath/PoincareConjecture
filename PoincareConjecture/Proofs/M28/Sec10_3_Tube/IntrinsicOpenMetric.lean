import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicCompetitors
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalDiffeomorph











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

omit [IsManifold (𝓡 3) ∞ M] in

theorem openSubtypeInverse_contMDiffOn (U : TopologicalSpace.Opens M)
    (hne : Nonempty U) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞
      (U.openPartialHomeomorphSubtypeCoe hne).symm (U : Set M) := by
  let e := U.openPartialHomeomorphSubtypeCoe hne
  intro y hy
  have heq : (Subtype.val ∘ e.symm) =ᶠ[𝓝 y] (id : M → M) := by
    filter_upwards [U.isOpen.mem_nhds hy] with z hz
    exact e.right_inv (by simpa only [e,
      TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] using hz)
  apply ContMDiffAt.contMDiffWithinAt
  apply (ContMDiffAt.subtypeVal_comp_iff U e.symm y).mp
  exact contMDiffAt_id.congr_of_eventuallyEq heq

omit [IsManifold (𝓡 3) ∞ M] in

theorem openSubtype_isLocalDiffeomorph (U : TopologicalSpace.Opens M) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (Subtype.val : U → M) := by
  intro x
  let hne : Nonempty U := ⟨x⟩
  let e := U.openPartialHomeomorphSubtypeCoe hne
  let d : PartialDiffeomorph (𝓡 3) (𝓡 3) U M ∞ := {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := by
      exact (contMDiff_subtype_val (I := 𝓡 3) (U := U)).contMDiffOn
    contMDiffOn_invFun := by
      change ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target
      rw [show e.target = (U : Set M) from
        U.openPartialHomeomorphSubtypeCoe_target hne]
      exact openSubtypeInverse_contMDiffOn U hne }
  change IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ d x
  refine ⟨d, ?_, Set.eqOn_refl _ _⟩
  · change x ∈ e.source
    simp only [e, TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_source, mem_univ]


def intrinsicOpenMetric (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M) :
    RiemannianMetric 3 U :=
  g.pullbackOfLocalDiffeomorph (Subtype.val : U → M)
    (openSubtype_isLocalDiffeomorph U)


@[simp] theorem intrinsicOpenMetric_inner (g : RiemannianMetric 3 M)
    (U : TopologicalSpace.Opens M) (x : U) (v w : TangentSpace (𝓡 3) x) :
    (intrinsicOpenMetric g U).inner x v w =
      g.inner (x : M)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → M) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → M) x w) := rfl



theorem intrinsicOpenMetric_pathELength (g : RiemannianMetric 3 M)
    (U : TopologicalSpace.Opens M) {η : ℝ → U} {a b : ℝ} (hab : a ≤ b)
    (hη : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 η (Icc a b)) :
    (intrinsicOpenMetric g U).pathELength η a b =
      g.pathELength (Subtype.val ∘ η) a b := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : U → Type _) :=
    ⟨(intrinsicOpenMetric g U).toRiemannianMetric⟩
  rcases eq_or_lt_of_le hab with rfl | hab
  · simp only [RiemannianMetric.pathELength, Manifold.pathELength_self]
  have hnormM (x : M) (v : TangentSpace (𝓡 3) x) :
      ENNReal.ofReal (g.tangentNorm x v) = ‖v‖ₑ := by
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  have hnormU (x : U) (v : TangentSpace (𝓡 3) x) :
      ENNReal.ofReal ((intrinsicOpenMetric g U).tangentNorm x v) = ‖v‖ₑ := by
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  change Manifold.pathELength (𝓡 3) η a b =
    Manifold.pathELength (𝓡 3) (Subtype.val ∘ η) a b
  rw [Manifold.pathELength_eq_lintegral_mfderivWithin_Icc,
    Manifold.pathELength_eq_lintegral_mfderivWithin_Icc]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t ht
  dsimp only
  have huniq : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc a b) t := by
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact uniqueDiffOn_Icc hab t ht
  have hi : MDifferentiableAt (𝓡 3) (𝓡 3) (Subtype.val : U → M) (η t) :=
    (contMDiff_subtype_val (I := 𝓡 3) (U := U) (n := 1)).mdifferentiable one_ne_zero (η t)
  rw [mfderiv_comp_mfderivWithin t hi
    (hη.mdifferentiableOn one_ne_zero t ht) huniq]
  rw [← hnormU, ← hnormM]
  rfl




theorem exists_intrinsicOpenMetric_path_lift (g : RiemannianMetric 3 M)
    (U : TopologicalSpace.Opens M) {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hγU : MapsTo γ (Icc a b) (U : Set M)) :
    ∃ η : ℝ → U, ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 η (Icc a b) ∧
      EqOn (Subtype.val ∘ η) γ (Icc a b) ∧
      (intrinsicOpenMetric g U).pathELength η a b = g.pathELength γ a b := by
  let hne : Nonempty U := ⟨⟨γ a, hγU ⟨le_rfl, hab⟩⟩⟩
  let e := U.openPartialHomeomorphSubtypeCoe hne
  let η := e.symm ∘ γ
  have hη : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 η (Icc a b) :=
    ((openSubtypeInverse_contMDiffOn U hne).of_le (by simp)).comp hγ hγU
  have heq : EqOn (Subtype.val ∘ η) γ (Icc a b) := by
    intro t ht
    exact e.right_inv (by simpa only [e,
      TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] using hγU ht)
  refine ⟨η, hη, heq, ?_⟩
  rw [intrinsicOpenMetric_pathELength g U hab hη]
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact Manifold.pathELength_congr heq



theorem intrinsicOpenMetric_edist (g : RiemannianMetric 3 M)
    (U : TopologicalSpace.Opens M) (p q : U) :
    (intrinsicOpenMetric g U).edist p q =
      intrinsicEDist g (U : Set M) (p : M) (q : M) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : U → Type _) :=
    ⟨(intrinsicOpenMetric g U).toRiemannianMetric⟩
  apply le_antisymm
  · rw [intrinsicEDist]
    apply le_sInf
    rintro L ⟨γ, hγ, h0, h1, hγU, rfl⟩
    obtain ⟨η, hη, heq, hlength⟩ := exists_intrinsicOpenMetric_path_lift g U
      zero_le_one hγ (fun t ht => hγU ⟨t, ht, rfl⟩)
    rw [← hlength]
    apply Manifold.riemannianEDist_le_pathELength hη _ _ zero_le_one
    · exact Subtype.ext ((heq (by norm_num)).trans h0)
    · exact Subtype.ext ((heq (by norm_num)).trans h1)
  · apply le_of_forall_gt_imp_ge_of_dense
    intro l hl
    obtain ⟨η, h0, h1, hη, hlen⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt hl
    have hpush : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1
        (Subtype.val ∘ η) (Icc (0 : ℝ) 1) :=
      (contMDiff_subtype_val (I := 𝓡 3) (U := U)).comp_contMDiffOn hη
    have hle := intrinsicEDist_le_pathELength g zero_le_one hpush
      (fun t (_ : t ∈ Icc (0 : ℝ) 1) => (η t).property)
    rw [← intrinsicOpenMetric_pathELength g U zero_le_one hη] at hle
    simpa only [Function.comp_apply, h0, h1] using hle.trans hlen.le

end PoincareConjecture.M28
