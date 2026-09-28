import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Flow.Complete.Local
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {X : (x : M) → TangentSpace (𝓡 n) x}


structure SmoothIntegralFamily (X : (x : M) → TangentSpace (𝓡 n) x)
    (V : Set M) (I : Set ℝ) (Φ : ℝ × M → M) : Prop where
  smooth : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ Φ (I ×ˢ V)
  orbit : ∀ y ∈ V, IsMIntegralCurveOn (I := 𝓡 n) (fun t => Φ (t, y)) X I

omit [IsManifold (𝓡 n) ∞ M] in
theorem SmoothIntegralFamily.mono {V W : Set M} {I J : Set ℝ} {Φ : ℝ × M → M}
    (h : SmoothIntegralFamily X V I Φ) (hW : W ⊆ V) (hJ : J ⊆ I) :
    SmoothIntegralFamily X W J Φ :=
  ⟨h.smooth.mono (prod_mono hJ hW), fun y hy => (h.orbit y (hW hy)).mono hJ⟩

omit [IsManifold (𝓡 n) ∞ M] in
theorem SmoothIntegralFamily.smooth_orbit {V : Set M} {I : Set ℝ} {Φ : ℝ × M → M}
    (h : SmoothIntegralFamily X V I Φ) {y : M} (hy : y ∈ V) :
    ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun t => Φ (t, y)) I :=
  h.smooth.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn (fun _ ht => ⟨ht, hy⟩)


theorem exists_uniform_smooth_localFlows
    (hX : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% X))
    {K : Set M} (hK : IsCompact K) :
    ∃ δ > 0, ∀ x ∈ K, ∃ (V : Set M) (Φ : ℝ × M → M),
      IsOpen V ∧ x ∈ V ∧ SmoothIntegralFamily X V (Ioo (-δ) δ) Φ ∧
        ∀ y ∈ V, Φ (0, y) = y := by
  let P : Set M → Prop := fun S =>
    ∃ δ > 0, ∀ x ∈ S, ∃ (V : Set M) (Φ : ℝ × M → M),
      IsOpen V ∧ x ∈ V ∧ SmoothIntegralFamily X V (Ioo (-δ) δ) Φ ∧
        ∀ y ∈ V, Φ (0, y) = y
  change P K
  refine hK.induction_on (p := P) ?_ ?_ ?_ ?_
  · exact ⟨1, zero_lt_one, fun _ hx => False.elim hx⟩
  · rintro S T hST ⟨δ, hδ, h⟩
    exact ⟨δ, hδ, fun x hx => h x (hST hx)⟩
  · rintro S T ⟨δ, hδ, hS⟩ ⟨ε, hε, hT⟩
    refine ⟨min δ ε, lt_min hδ hε, ?_⟩
    intro x hx
    rcases hx with hx | hx
    · obtain ⟨V, Φ, hV, hxV, hΦ, hi⟩ := hS x hx
      exact ⟨V, Φ, hV, hxV, hΦ.mono subset_rfl
        (Ioo_subset_Ioo (neg_le_neg (min_le_left _ _)) (min_le_left _ _)), hi⟩
    · obtain ⟨V, Φ, hV, hxV, hΦ, hi⟩ := hT x hx
      exact ⟨V, Φ, hV, hxV, hΦ.mono subset_rfl
        (Ioo_subset_Ioo (neg_le_neg (min_le_right _ _)) (min_le_right _ _)), hi⟩
  · intro x _
    obtain ⟨V, δ, Φ, hV, hxV, hδ, hs, hi, hd⟩ := exists_smooth_localFlow hX x
    exact ⟨V, mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hxV), δ, hδ,
      fun y hy => ⟨V, Φ, hV, hy, ⟨hs, hd⟩, hi⟩⟩

variable [T2Space M]


theorem SmoothIntegralFamily.glue
    (hX : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) 1 (T% X))
    {V : Set M} (hV : IsOpen V) {a b c d s : ℝ} {Φ Ψ : ℝ × M → M}
    (hΦ : SmoothIntegralFamily X V (Ioo a b) Φ)
    (hΨ : SmoothIntegralFamily X V (Ioo c d) Ψ)
    (hs : s ∈ Ioo a b ∩ Ioo c d) (he : ∀ y ∈ V, Φ (s, y) = Ψ (s, y)) :
    ∃ Ξ : ℝ × M → M, SmoothIntegralFamily X V (Ioo a b ∪ Ioo c d) Ξ ∧
      EqOn Ξ Φ (Ioo a b ×ˢ V) ∧ EqOn Ξ Ψ (Ioo c d ×ˢ V) := by
  classical
  let Ξ : ℝ × M → M := fun p => if p.1 ∈ Ioo a b then Φ p else Ψ p
  have heΦ : EqOn Ξ Φ (Ioo a b ×ˢ V) := fun _ hp => if_pos hp.1
  have heΨ : EqOn Ξ Ψ (Ioo c d ×ˢ V) := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    exact eqOn_piecewise_of_isMIntegralCurveOn_Ioo hX (hΦ.orbit y hy)
      (hΨ.orbit y hy) hs (he y hy) ht
  refine ⟨Ξ, ⟨?_, ?_⟩, heΦ, heΨ⟩
  · rintro ⟨t, y⟩ ⟨ht | ht, hy⟩
    · have hev : Ξ =ᶠ[𝓝 (t, y)] Φ :=
        Filter.Eventually.mono ((isOpen_Ioo.prod hV).mem_nhds ⟨ht, hy⟩)
          (fun _ hp => heΦ hp)
      exact ((hΦ.smooth.contMDiffAt ((isOpen_Ioo.prod hV).mem_nhds ⟨ht, hy⟩)).congr_of_eventuallyEq
        hev).contMDiffWithinAt
    · have hev : Ξ =ᶠ[𝓝 (t, y)] Ψ :=
        Filter.Eventually.mono ((isOpen_Ioo.prod hV).mem_nhds ⟨ht, hy⟩)
          (fun _ hp => heΨ hp)
      exact ((hΨ.smooth.contMDiffAt ((isOpen_Ioo.prod hV).mem_nhds ⟨ht, hy⟩)).congr_of_eventuallyEq
        hev).contMDiffWithinAt
  · intro y hy
    exact isMIntegralCurveOn_piecewise hX (hΦ.orbit y hy) (hΨ.orbit y hy) hs (he y hy)

omit [IsManifold (𝓡 n) ∞ M] [T2Space M] in

theorem SmoothIntegralFamily.restart
    {V W : Set M} {a b δ s : ℝ} {Φ Ψ : ℝ × M → M}
    (hV : IsOpen V) (hW : IsOpen W) (hs : s ∈ Ioo a b)
    (hΦ : SmoothIntegralFamily X V (Ioo a b) Φ)
    (hΨ : SmoothIntegralFamily X W (Ioo (-δ) δ) Ψ) :
    IsOpen (V ∩ (fun y => Φ (s, y)) ⁻¹' W) ∧
      SmoothIntegralFamily X (V ∩ (fun y => Φ (s, y)) ⁻¹' W)
        (Ioo (s - δ) (s + δ)) (fun p => Ψ (p.1 - s, Φ (s, p.2))) := by
  have hslice (y : M) (hy : y ∈ V) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ (fun z => Φ (s, z)) y :=
    (hΦ.smooth.contMDiffAt ((isOpen_Ioo.prod hV).mem_nhds ⟨hs, hy⟩)).comp y
      (contMDiffAt_const.prodMk contMDiffAt_id)
  refine ⟨(show ContinuousOn (fun y => Φ (s, y)) V from
    fun y hy => (hslice y hy).continuousAt.continuousWithinAt).isOpen_inter_preimage hV hW,
    ⟨?_, ?_⟩⟩
  · rintro ⟨t, y⟩ ⟨ht, hy⟩
    have hsecond : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
      (fun p : ℝ × M => Φ (s, p.2)) (t, y) :=
      (hΦ.smooth.contMDiffAt ((isOpen_Ioo.prod hV).mem_nhds
        (show (s, y) ∈ Ioo a b ×ˢ V from ⟨hs, hy.1⟩))).comp
        (t, y) (contMDiffAt_const.prodMk contMDiffAt_snd)
    have hp : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun p : ℝ × M => (p.1 - s, Φ (s, p.2))) (t, y) :=
      (contMDiffAt_fst.sub contMDiffAt_const).prodMk hsecond
    exact ((hΨ.smooth.contMDiffAt ((isOpen_Ioo.prod hW).mem_nhds
      (show (t - s, Φ (s, y)) ∈ Ioo (-δ) δ ×ˢ W from
        ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, hy.2⟩))).comp (t, y) hp).contMDiffWithinAt
  · intro y hy
    have hd := (hΨ.orbit _ hy.2).comp_add (-s)
    apply hd.mono
    intro t ht
    constructor <;> linarith [ht.1, ht.2]

end Poincare.Manifold
