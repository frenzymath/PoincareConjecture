import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.LocalInverse
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.Lifting.Compact
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.Nonconjugacy
import Mathlib.Analysis.Calculus.MeanValue














noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Function
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem exists_hasDerivWithinAt_lift
    {f : EuclideanSpace ℝ (Fin n) → M} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hbij : ∀ x ∈ U, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x))
    {c : ℝ → M} {l : ℝ → EuclideanSpace ℝ (Fin n)} {s : Set ℝ} {t : ℝ}
    (hc : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ c t)
    (hl : ContinuousWithinAt l s t) (ht : t ∈ s) (hlt : l t ∈ U)
    (hproj : EqOn (f ∘ l) c s) :
    ∃ w : EuclideanSpace ℝ (Fin n), HasDerivWithinAt l w s t ∧
      mfderiv (𝓡 n) (𝓡 n) f (l t) w = mfderiv 𝓘(ℝ, ℝ) (𝓡 n) c t 1 := by
  obtain ⟨e, hlt', hsub, heq, _, hismooth⟩ := exists_smooth_inverse_branch hU hf hbij hlt
  have hct : c t ∈ e.target := by
    rw [← hproj ht]
    change f (l t) ∈ e.target
    rw [← heq hlt']
    exact e.map_source hlt'
  let k : ℝ → EuclideanSpace ℝ (Fin n) := e.symm ∘ c
  have hkt : k t = l t := by
    change e.symm (c t) = l t
    rw [← hproj ht]
    change e.symm (f (l t)) = l t
    rw [← heq hlt']
    exact e.left_inv hlt'
  have hk : ContDiffAt ℝ ∞ k t := contMDiffAt_iff_contDiffAt.mp
    ((hismooth.contMDiffAt (e.open_target.mem_nhds hct)).comp t hc)
  have hevent : l =ᶠ[𝓝[s] t] k := by
    filter_upwards [hl.preimage_mem_nhdsWithin (e.open_source.mem_nhds hlt'),
      self_mem_nhdsWithin] with u hu hus
    change l u = e.symm (c u)
    rw [← hproj hus]
    change l u = e.symm (f (l u))
    rw [← heq hu, e.left_inv hu]
  have hfk : (f ∘ k) =ᶠ[𝓝 t] c := by
    filter_upwards [hc.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds hct)] with u hu
    change f (e.symm (c u)) = c u
    rw [← heq (e.map_target hu), e.right_inv hu]
  have hdk := (hk.differentiableAt (by simp)).hasDerivAt
  refine ⟨deriv k t, hdk.hasDerivWithinAt.congr_of_eventuallyEq hevent hkt.symm, ?_⟩
  have hfkt := (hf.contMDiffAt (hU.mem_nhds (hkt.symm ▸ hlt))).mdifferentiableAt
    (by simp)
  have hd := mfderiv_comp t hfkt hdk.differentiableAt.mdifferentiableAt
  rw [hfk.mfderiv_eq, mfderiv_eq_fderiv] at hd
  have hd1 := congrArg (fun A : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) => A 1) hd
  change mfderiv 𝓘(ℝ, ℝ) (𝓡 n) c t 1 =
    mfderiv (𝓡 n) (𝓡 n) f (k t) (fderiv ℝ k t 1) at hd1
  simp only [TangentSpace] at hd1 ⊢
  rw [fderiv_eq_smul_deriv, one_smul, hkt] at hd1
  exact hd1.symm



theorem norm_sub_le_of_continuous_lift
    (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hbij : ∀ x ∈ U, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x))
    (hlower : ∀ x ∈ U, ∀ w : EuclideanSpace ℝ (Fin n),
      ‖w‖ / 2 ≤ g.tangentNorm (f x) (mfderiv (𝓡 n) (𝓡 n) f x w))
    {c : ℝ → M} {l : ℝ → EuclideanSpace ℝ (Fin n)} {a b C : ℝ} (hab : a ≤ b)
    (hc : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ c t)
    (hspeed : ∀ t ∈ Icc a b, g.tangentNorm (c t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) c t 1) ≤ C)
    (hl : ContinuousOn l (Icc a b)) (hlu : MapsTo l (Icc a b) U)
    (hproj : EqOn (f ∘ l) c (Icc a b)) : ‖l b - l a‖ ≤ 2 * C * (b - a) := by
  choose w hw hproject using fun t (ht : t ∈ Icc a b) =>
    exists_hasDerivWithinAt_lift hU hf hbij (hc t ht) (hl t ht) ht (hlu ht) hproj
  let W : ℝ → EuclideanSpace ℝ (Fin n) := fun t =>
    if ht : t ∈ Icc a b then w t ht else 0
  have hW (t) (ht : t ∈ Icc a b) : W t = w t ht := dif_pos ht
  apply norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht => hW t ht ▸ hw t ht) ?_ b (right_mem_Icc.mpr hab)
  intro t ht
  have ht' : t ∈ Icc a b := Ico_subset_Icc_self ht
  rw [hW t ht']
  have h := hlower (l t) (hlu ht') (w t ht')
  rw [hproject t ht'] at h
  have hvalue := congrArg (fun x : M => g.tangentNorm x
    (show EuclideanSpace ℝ (Fin n) from mfderiv 𝓘(ℝ, ℝ) (𝓡 n) c t 1)) (hproj ht')
  change g.tangentNorm (f (l t)) _ = g.tangentNorm (c t) _ at hvalue
  rw [hvalue] at h
  linarith [hspeed t ht']



theorem isLocalHomeomorph_domRestrict_of_nonsingular
    {f : EuclideanSpace ℝ (Fin n) → M} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hbij : ∀ x ∈ U, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x)) :
    IsLocalHomeomorph (U.domRestrict f) := by
  intro x
  obtain ⟨e, hx, _, heq, _, _⟩ := exists_smooth_inverse_branch hU hf hbij x.2
  let e' : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M :=
    { e with
      toFun := f
      map_source' := fun z hz => heq hz ▸ e.map_source hz
      left_inv' := fun z hz => by rw [← heq hz]; exact e.left_inv hz
      right_inv' := fun z hz => by
        change f (e.symm z) = z
        rw [← heq (e.map_target hz)]
        exact e.right_inv hz
      continuousOn_toFun := e.continuousOn.congr heq.symm }
  refine ⟨e'.subtypeRestr (s := ⟨U, hU⟩) ⟨x⟩, ?_, rfl⟩
  simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hx


theorem isCompact_norm_sublevel_in_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {r R : ℝ} (hrR : r < R) :
    IsCompact {x : Metric.ball (0 : E) R | ‖(x : E)‖ ≤ r} := by
  apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
  have heq : Subtype.val '' {x : Metric.ball (0 : E) R | ‖(x : E)‖ ≤ r} =
      Metric.closedBall (0 : E) r := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      have hxr : ‖x‖ ≤ r := by simpa using hx
      exact ⟨⟨x, by simpa using hxr.trans_lt hrR⟩, hxr, rfl⟩
  rw [heq]
  exact isCompact_closedBall _ _




theorem exists_bounded_lift_of_lower_differential [T2Space M]
    (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M} {R C : ℝ}
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f (Metric.ball 0 R))
    (hbij : ∀ x ∈ Metric.ball 0 R, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x))
    (hlower : ∀ x ∈ Metric.ball 0 R, ∀ w : EuclideanSpace ℝ (Fin n),
      ‖w‖ / 2 ≤ g.tangentNorm (f x) (mfderiv (𝓡 n) (𝓡 n) f x w))
    {c : ℝ → M} (hc : ∀ t ∈ Icc (0 : ℝ) 1, ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ c t)
    (hC : 0 ≤ C)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1, g.tangentNorm (c t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) c t 1) ≤ C)
    (y : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) (hy : f y = c 0)
    (hshort : ‖(y : EuclideanSpace ℝ (Fin n))‖ + 2 * C < R) :
    ∃ l : ℝ → Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R,
      ContinuousOn l (Icc 0 1) ∧ l 0 = y ∧
      EqOn (fun t => f (l t)) c (Icc 0 1) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ‖(l t : EuclideanSpace ℝ (Fin n)) - y‖ ≤ 2 * C * t := by
  let F := (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R).domRestrict f
  have hlocal : IsLocalHomeomorph F :=
    isLocalHomeomorph_domRestrict_of_nonsingular Metric.isOpen_ball hf hbij
  let clamp : ℝ → ℝ := fun t => (projIcc (0 : ℝ) 1 zero_le_one t : ℝ)
  have hclamp : Continuous clamp := continuous_subtype_val.comp continuous_projIcc
  have hclamp_mem : ∀ t, clamp t ∈ Icc (0 : ℝ) 1 := fun t => (projIcc 0 1 zero_le_one t).2
  let c' := c ∘ clamp
  have hc' : Continuous c' :=
    (show ContinuousOn c (Icc (0 : ℝ) 1) from fun t ht =>
      (hc t ht).continuousAt.continuousWithinAt).comp_continuous hclamp hclamp_mem
  have heq : EqOn c' c (Icc (0 : ℝ) 1) := by
    intro t ht
    simp only [c', comp_apply, clamp, projIcc_of_mem zero_le_one ht]
  let K : Set (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) :=
    {x | ‖(x : EuclideanSpace ℝ (Fin n))‖ ≤ ‖(y : EuclideanSpace ℝ (Fin n))‖ + 2 * C}
  have hK : IsCompact K := isCompact_norm_sublevel_in_ball hshort
  have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
      (l : ℝ → Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)
      (hl : ContinuousOn l (Icc 0 t)) (h0 : l 0 = y)
      (hproj : EqOn (F ∘ l) c (Icc 0 t)) :
      ‖(l t : EuclideanSpace ℝ (Fin n)) - y‖ ≤ 2 * C * t := by
    have h := norm_sub_le_of_continuous_lift g Metric.isOpen_ball hf hbij hlower ht.1
      (fun s hs => hc s ⟨hs.1, hs.2.trans ht.2⟩)
      (fun s hs => hspeed s ⟨hs.1, hs.2.trans ht.2⟩)
      (continuous_subtype_val.comp_continuousOn hl) (fun s _ => (l s).2) hproj
    simpa only [Function.comp_apply, h0, sub_zero] using h
  obtain ⟨l, hl, h0, hproj⟩ := exists_lift_of_compact_prefixes hlocal hc'
    (hy.trans (heq (by simp)).symm) hK (by
      intro t ht l hl h0 hproj
      have h := hbound t ht l hl h0
        (hproj.trans (heq.mono (Icc_subset_Icc le_rfl ht.2)))
      change ‖(l t : EuclideanSpace ℝ (Fin n))‖ ≤ ‖(y : EuclideanSpace ℝ (Fin n))‖ + 2 * C
      have htri := norm_add_le ((l t : EuclideanSpace ℝ (Fin n)) - y) (y : EuclideanSpace ℝ (Fin n))
      rw [sub_add_cancel] at htri
      have hmul := mul_le_mul_of_nonneg_left ht.2 (show 0 ≤ 2 * C by positivity)
      linarith)
  have hprojc : EqOn (F ∘ l) c (Icc (0 : ℝ) 1) := hproj.trans heq
  refine ⟨l, hl, h0, hprojc, ?_⟩
  intro t ht
  exact hbound t ht l (hl.mono (Icc_subset_Icc le_rfl ht.2)) h0
    (hprojc.mono (Icc_subset_Icc le_rfl ht.2))

end PoincareConjecture
