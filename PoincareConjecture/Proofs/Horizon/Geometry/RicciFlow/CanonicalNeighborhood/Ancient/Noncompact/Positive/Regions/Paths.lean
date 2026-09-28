import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Transport.Distance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.NoncompactKappa.Positive

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  (g : RiemannianMetric 3 M) {U V : Set M} {x y z : M}

theorem intrinsicEDist_mono (hUV : U ⊆ V) :
    intrinsicEDist g V x y ≤ intrinsicEDist g U x y := by
  apply sInf_le_sInf
  rintro L ⟨γ, hγ, h0, h1, hU, hL⟩
  exact ⟨γ, hγ, h0, h1, hU.trans hUV, hL⟩

theorem intrinsicEDist_le_pathELength_on {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (h0 : γ a = x) (h1 : γ b = y) (hU : MapsTo γ (Icc a b) U) :
    intrinsicEDist g U x y ≤ g.pathELength γ a b := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let η := fun t : ℝ => a + t * (b - a)
  have hη0 : η 0 = a := by simp [η]
  have hη1 : η 1 = b := by simp [η]
  have hmap : MapsTo η (Icc 0 1) (Icc a b) := by
    intro t ht
    dsimp [η]
    constructor <;> nlinarith [ht.1, ht.2]
  apply g.intrinsicEDist_le_of_path
    (hγ.comp (show ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 η from by
      rw [contMDiff_iff_contDiff]; dsimp [η]; fun_prop).contMDiffOn hmap)
    (by simpa only [Function.comp_apply, hη0] using h0)
    (by simpa only [Function.comp_apply, hη1] using h1)
    (image_subset_iff.mpr (hU.comp hmap))
  change Manifold.pathELength (𝓡 3) (γ ∘ η) 0 1 ≤ Manifold.pathELength (𝓡 3) γ a b
  apply le_of_eq
  simpa only [hη0, hη1] using Manifold.pathELength_comp_of_monotoneOn
    zero_le_one (show MonotoneOn η (Icc 0 1) by intro s _ t _ hst; dsimp [η]; gcongr)
    (by dsimp [η]; fun_prop) (by simpa only [hη0, hη1] using hγ.mdifferentiableOn one_ne_zero)

theorem exists_locally_constant_intrinsic_path {r : ℝ≥0∞}
    (hr : intrinsicEDist g U x y < r) {a b : ℝ} (hab : a < b) :
    ∃ γ : ℝ → M, γ a = x ∧ γ b = y ∧
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 γ ∧ g.pathELength γ a b < r ∧
      γ =ᶠ[𝓝 a] (fun _ => x) ∧ γ =ᶠ[𝓝 b] (fun _ => y) ∧ ∀ t, γ t ∈ U := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨L, ⟨γ, hγ, hγ0, hγ1, hγU, rfl⟩, hL⟩ := sInf_lt_iff.mp hr
  obtain ⟨a', haa', ha'b⟩ := exists_between hab
  obtain ⟨b', ha'b', hb'b⟩ := exists_between ha'b
  let η := fun t : ℝ => Real.smoothTransition ((b' - a')⁻¹ * (t - a'))
  have hη (t : ℝ) : η t ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hleft (t : ℝ) (ht : t < a') : η t = 0 := by
    simp only [η, Real.smoothTransition.zero_iff_nonpos]
    apply mul_nonpos_of_nonneg_of_nonpos
    · exact inv_nonneg.mpr (sub_nonneg.mpr ha'b'.le)
    · linarith
  have hright (t : ℝ) (ht : b' < t) : η t = 1 := by
    simp only [η, Real.smoothTransition.eq_one_iff_one_le, inv_mul_eq_div]
    rw [one_le_div₀] <;> linarith
  refine ⟨γ ∘ η, by simp [hleft a haa', hγ0], by simp [hright b hb'b, hγ1],
    ?_, ?_, ?_, ?_, fun t => hγU ⟨η t, hη t, rfl⟩⟩
  · rw [← contMDiffOn_univ]
    exact hγ.comp (show ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 η from by
      rw [contMDiff_iff_contDiff]; dsimp [η]; fun_prop).contMDiffOn (fun t _ => hη t)
  · have hmono : MonotoneOn η (Icc a b) := by
      apply Monotone.monotoneOn
      apply Real.smoothTransition.monotone.comp
      intro s t hst
      dsimp only
      gcongr
    have hdiff : DifferentiableOn ℝ η (Icc a b) := by
      dsimp [η]
      apply (ContDiff.contDiffOn _).differentiableOn one_ne_zero
      fun_prop
    have heq : g.pathELength (γ ∘ η) a b = g.pathELength γ (η a) (η b) :=
      Manifold.pathELength_comp_of_monotoneOn (I := 𝓡 3) (γ := γ) (f := η)
      hab.le hmono hdiff (by
        simpa only [hleft a haa', hright b hb'b] using hγ.mdifferentiableOn one_ne_zero)
    have heq' : g.pathELength (γ ∘ η) a b = g.pathELength γ 0 1 := by
      simpa only [hleft a haa', hright b hb'b] using heq
    exact heq'.trans_lt hL
  · filter_upwards [Iio_mem_nhds haa'] with t ht
    simp [hleft t ht, hγ0]
  · filter_upwards [Ioi_mem_nhds hb'b] with t ht
    simp [hright t ht, hγ1]

theorem intrinsicEDist_triangle :
    intrinsicEDist g U x z ≤ intrinsicEDist g U x y + intrinsicEDist g U y z := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  classical
  apply le_of_forall_gt
  intro r hr
  obtain ⟨u, hu, v, hv, huv⟩ := ENNReal.exists_add_lt_of_add_lt hr
  obtain ⟨γ₁, hγ₁0, _, hγ₁, hL₁, _, hconst₁, hU₁⟩ :=
    exists_locally_constant_intrinsic_path g hu zero_lt_one
  obtain ⟨γ₂, _, hγ₂2, hγ₂, hL₂, hconst₂, _, hU₂⟩ :=
    exists_locally_constant_intrinsic_path g hv one_lt_two
  let γ := piecewise (Iic 1) γ₁ γ₂
  have hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 γ :=
    ContMDiff.piecewise_Iic hγ₁ hγ₂ (hconst₁.trans hconst₂.symm)
  have hbound := intrinsicEDist_le_pathELength_on g (U := U) (x := x) (y := z)
    zero_lt_two hγ.contMDiffOn
    (by simp [γ, hγ₁0]) (by simp [γ, hγ₂2])
    (show MapsTo γ (Icc 0 2) U by
      intro t _
      by_cases ht : t ≤ 1
      · simpa [γ, ht] using hU₁ t
      · simpa [γ, ht] using hU₂ t)
  apply hbound.trans_lt (lt_trans ?_ huv)
  change Manifold.pathELength (𝓡 3) γ 0 2 < u + v
  rw [← Manifold.pathELength_add zero_le_one one_le_two]
  have hlen₁ : Manifold.pathELength (𝓡 3) γ 0 1 = g.pathELength γ₁ 0 1 := by
    apply Manifold.pathELength_congr
    intro t ht
    simp [γ, ht.2]
  have hlen₂ : Manifold.pathELength (𝓡 3) γ 1 2 = g.pathELength γ₂ 1 2 := by
    apply Manifold.pathELength_congr_Ioo
    intro t ht
    simp [γ, ht.1]
  rw [hlen₁, hlen₂]
  exact ENNReal.add_lt_add hL₁ hL₂

theorem intrinsicEDist_comm : intrinsicEDist g U x y = intrinsicEDist g U y x := by
  suffices h : ∀ x y, intrinsicEDist g U y x ≤ intrinsicEDist g U x y from
    le_antisymm (h y x) (h x y)
  intro x y
  apply le_sInf
  rintro L ⟨γ, hγ, hγ0, hγ1, hγU, rfl⟩
  let η := fun t : ℝ => 1 - t
  have hmap : MapsTo η (Icc 0 1) (Icc 0 1) := by
    intro t ht
    exact ⟨by dsimp [η]; linarith [ht.2], by dsimp [η]; linarith [ht.1]⟩
  have hη : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 η := by
    rw [contMDiff_iff_contDiff]
    fun_prop
  apply g.intrinsicEDist_le_of_path (hγ.comp hη.contMDiffOn hmap)
    (by simpa [η] using hγ1) (by simpa [η] using hγ0)
    (image_subset_iff.mpr (fun t ht => hγU ⟨η t, hmap ht, rfl⟩))
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hanti : AntitoneOn η (Icc 0 1) := fun _ _ _ _ h => sub_le_sub_left h 1
  have heq : g.pathELength (γ ∘ η) 0 1 = g.pathELength γ (η 1) (η 0) :=
    Manifold.pathELength_comp_of_antitoneOn zero_le_one hanti
      (by dsimp [η]; fun_prop) (by simpa [η] using hγ.mdifferentiableOn one_ne_zero)
  exact (by simpa [η] using heq : g.pathELength (γ ∘ η) 0 1 = g.pathELength γ 0 1).le

end PoincareConjecture.NoncompactKappa.Positive
