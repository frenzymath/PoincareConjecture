import PoincareConjecture.Proofs.Horizon.Analysis.ODE.LocalFlow.Smooth
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.Instances.Real









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem exists_smooth_localFlow_on_open
    {X : (x : M) → TangentSpace (𝓡 n) x} {U : Set M} (hU : IsOpen U)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% X) U)
    {x : M} (hx : x ∈ U) :
    ∃ (V : Set M) (δ : ℝ) (Φ : ℝ × M → M),
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ 0 < δ ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ Φ (Ioo (-δ) δ ×ˢ V) ∧
      (∀ y ∈ V, Φ (0, y) = y) ∧
      ∀ y ∈ V, (∀ t ∈ Ioo (-δ) δ, Φ (t, y) ∈ U) ∧
        IsMIntegralCurveOn (I := 𝓡 n) (fun t => Φ (t, y)) X (Ioo (-δ) δ) := by
  let c := extChartAt (𝓡 n) x
  have hc (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ c.target) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm z :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) x hz).contMDiffAt
      (extChartAt_target_mem_nhds' hz)
  have hi (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ c.target) :
      (mfderiv (𝓡 n) (𝓡 n) c.symm z).IsInvertible := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm hz
  have hchart : ContMDiffOn (𝓡 n) (𝓡 n) ∞ c c.source := by
    simpa only [c, extChartAt_source] using
      (contMDiffOn_extChartAt (I := 𝓡 n) (x := x) (n := ∞))
  let A := c.target ∩ c.symm ⁻¹' U
  have hAo : IsOpen A :=
    (show ContinuousOn c.symm c.target from fun z hz =>
      (hc z hz).continuousAt.continuousWithinAt).isOpen_inter_preimage
        (isOpen_extChartAt_target x) hU
  have hxA : c x ∈ A := ⟨mem_extChartAt_target x,
    by simpa only [mem_preimage, c.left_inv (mem_extChartAt_source x)] using hx⟩
  let F := VectorField.mpullback (𝓡 n) (𝓡 n) c.symm X
  have hF : ContDiffOn ℝ ∞ F A := by
    intro z hz
    apply (contMDiffAt_vectorSpace_iff_contDiffAt.mp ?_).contDiffWithinAt
    exact (hX.contMDiffAt (hU.mem_nhds hz.2)).mpullback_vectorField_preimage
      (hc z hz.1) (hi z hz.1) (by simp)
  have hpush (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ A) :
      mfderiv (𝓡 n) (𝓡 n) c.symm z (F z) = X (c.symm z) := by
    exact (hi z hz.1).self_apply_inverse _
  obtain ⟨B, δ, q, hBo, hxB, hBA, hδ, hq, hq0, hqU, hqd⟩ :=
    Poincare.ODE.LocalFlow.exists_smooth_localFlow hAo hF hxA
  let V := c.source ∩ c ⁻¹' B
  have hVo : IsOpen V := hchart.continuousOn.isOpen_inter_preimage
    (isOpen_extChartAt_source x) hBo
  have hVU : V ⊆ U := by
    intro y hy
    have hm := (hBA hy.2).2
    simpa only [mem_preimage, c.left_inv hy.1] using hm
  let Φ : ℝ × M → M := fun z => c.symm (q (c z.2, z.1))
  have hpoint (t : ℝ) (y : M) (hy : y ∈ V) (ht : t ∈ Ioo (-δ) δ) :
      q (c y, t) ∈ A := hqU _ hy.2 t ht
  have hsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ Φ
      (Ioo (-δ) δ ×ˢ V) := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    have hcd := hchart.contMDiffAt (extChartAt_source_mem_nhds' hy.1)
    have hpair : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n))
        ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞ (fun z : ℝ × M => (c z.2, z.1)) (t, y) :=
      (hcd.comp (t, y) contMDiffAt_snd).prodMk contMDiffAt_fst
    have hqm : ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 n) ∞ q (c y, t) := by
      have hqt : ContDiffAt ℝ ∞ q (c y, t) :=
        hq.contDiffAt ((hBo.prod isOpen_Ioo).mem_nhds ⟨hy.2, ht⟩)
      rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
      exact hqt.contMDiffAt
    exact ((hc _ (hpoint t y hy ht).1).comp (t, y)
      (hqm.comp (t, y) hpair)).contMDiffWithinAt
  refine ⟨V, δ, Φ, hVo, ⟨mem_extChartAt_source x, hxB⟩, hVU, hδ, hsmooth, ?_, ?_⟩
  · intro y hy
    change c.symm (q (c y, 0)) = y
    rw [hq0 _ hy.2, c.left_inv hy.1]
  · intro y hy
    refine ⟨fun t ht => (hpoint t y hy ht).2, ?_⟩
    intro t ht
    have hd := ((hc _ (hpoint t y hy ht).1).mdifferentiableAt (by simp)).hasMFDerivAt.comp t
      (hqd _ hy.2 t ht).hasFDerivAt.hasMFDerivAt
    apply HasMFDerivAt.hasMFDerivWithinAt
    apply hd.congr_mfderiv
    apply ContinuousLinearMap.ext
    intro a
    change mfderiv (𝓡 n) (𝓡 n) c.symm (q (c y, t)) (a • F (q (c y, t))) =
      a • X (c.symm (q (c y, t)))
    rw [map_smul, hpush _ (hpoint t y hy ht)]



theorem exists_uniform_smooth_local_flows
    {X : (x : M) → TangentSpace (𝓡 n) x} {U K : Set M} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% X) U) :
    ∃ δ > 0, ∀ x ∈ K, ∃ (V : Set M) (Φ : ℝ × M → M),
      IsOpen V ∧ x ∈ V ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ Φ (Ioo (-δ) δ ×ˢ V) ∧
      (∀ y ∈ V, Φ (0, y) = y) ∧
      ∀ y ∈ V, (∀ t ∈ Ioo (-δ) δ, Φ (t, y) ∈ U) ∧
        IsMIntegralCurveOn (I := 𝓡 n) (fun t => Φ (t, y)) X (Ioo (-δ) δ) := by
  let P : Set M → Prop := fun S => ∃ δ > 0, ∀ x ∈ S, ∃ (V : Set M) (Φ : ℝ × M → M),
    IsOpen V ∧ x ∈ V ∧
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ Φ (Ioo (-δ) δ ×ˢ V) ∧
    (∀ y ∈ V, Φ (0, y) = y) ∧
    ∀ y ∈ V, (∀ t ∈ Ioo (-δ) δ, Φ (t, y) ∈ U) ∧
      IsMIntegralCurveOn (I := 𝓡 n) (fun t => Φ (t, y)) X (Ioo (-δ) δ)
  change P K
  refine hK.induction_on (p := P) ?_ ?_ ?_ ?_
  · exact ⟨1, zero_lt_one, fun _ hx => False.elim hx⟩
  · rintro S T hST ⟨δ, hδ, h⟩
    exact ⟨δ, hδ, fun x hx => h x (hST hx)⟩
  · rintro S T ⟨δ, hδ, hS⟩ ⟨ε, hε, hT⟩
    refine ⟨min δ ε, lt_min hδ hε, ?_⟩
    intro x hx
    rcases hx with hx | hx
    · obtain ⟨V, Φ, hV, hxV, hs, hinit, horbit⟩ := hS x hx
      have hsub : Ioo (-min δ ε) (min δ ε) ⊆ Ioo (-δ) δ :=
        Ioo_subset_Ioo (neg_le_neg (min_le_left _ _)) (min_le_left _ _)
      exact ⟨V, Φ, hV, hxV, hs.mono (prod_mono_left hsub), hinit,
        fun y hy => ⟨fun t ht => (horbit y hy).1 t (hsub ht), (horbit y hy).2.mono hsub⟩⟩
    · obtain ⟨V, Φ, hV, hxV, hs, hinit, horbit⟩ := hT x hx
      have hsub : Ioo (-min δ ε) (min δ ε) ⊆ Ioo (-ε) ε :=
        Ioo_subset_Ioo (neg_le_neg (min_le_right _ _)) (min_le_right _ _)
      exact ⟨V, Φ, hV, hxV, hs.mono (prod_mono_left hsub), hinit,
        fun y hy => ⟨fun t ht => (horbit y hy).1 t (hsub ht), (horbit y hy).2.mono hsub⟩⟩
  · intro x hx
    obtain ⟨V, δ, Φ, hV, hxV, _, hδ, hs, hinit, horbit⟩ :=
      exists_smooth_localFlow_on_open hU hX (hKU hx)
    refine ⟨V, mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hxV), δ, hδ, ?_⟩
    exact fun y hy => ⟨V, Φ, hV, hy, hs, hinit, horbit⟩



theorem exists_uniform_local_integralCurves
    {X : (x : M) → TangentSpace (𝓡 n) x} {U K : Set M} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% X) U) :
    ∃ δ > 0, ∀ x ∈ K, ∃ γ : ℝ → M, γ 0 = x ∧
      (∀ t ∈ Ioo (-δ) δ, γ t ∈ U) ∧
      IsMIntegralCurveOn (I := 𝓡 n) γ X (Ioo (-δ) δ) := by
  obtain ⟨δ, hδ, hlocal⟩ := exists_uniform_smooth_local_flows hU hK hKU hX
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  obtain ⟨V, Φ, _, hxV, _, hinit, horbit⟩ := hlocal x hx
  exact ⟨fun t => Φ (t, x), hinit x hxV, horbit x hxV⟩

end Poincare.Manifold
