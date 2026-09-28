import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.EndBall.TerminalSlices

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap.AnnularEndFamily

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "IP" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)
local notation "IT" => ModelWithCorners.prod 𝓘(Real, Real) (𝓡 1)

private theorem exists_common_strict_upper_bound
    {ι : Type*} [Fintype ι] (c : ι → Real) {l b : Real}
    (hlb : l < b) (hc : ∀ i, c i < b) :
    ∃ a : Real, l < a ∧ a < b ∧ ∀ i, c i < a := by
  classical
  let s := insert l (Finset.univ.image c)
  have hs : s.Nonempty := ⟨l, Finset.mem_insert_self _ _⟩
  have hmax : s.max' hs < b := (Finset.max'_lt_iff s hs).mpr (by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hlb
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact hc i)
  obtain ⟨a, hma, hab⟩ := exists_between hmax
  refine ⟨a, (s.le_max' l (Finset.mem_insert_self _ _)).trans_lt hma, hab, ?_⟩
  intro i
  exact (s.le_max' (c i) (Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))).trans_lt hma

variable {v : E3} {g : S2 → E3} {B : Set Real} {C : Set S2}

theorem exists_lower_common_physical_annuli
    (ends : AnnularEndFamily v g B C)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g) (hv : ‖v‖ = 1) :
    ∃ a δ : Real, 0 < δ ∧ ends.lowerBound < a - δ ∧
      a + δ < ends.lowerCut - δ ∧
      (∀ i : ends.LowerCutIndex, i.1.1.center < a - δ) ∧
      ∃ T : ends.LowerCutIndex → OpenPartialHomeomorph (S1 × Real) S2,
        (∀ i, (T i).source = univ ×ˢ Ioo (a - δ) (ends.lowerCut + δ)) ∧
        (∀ i, ContMDiffOn IP (𝓡 2) ∞ (T i) (T i).source) ∧
        (∀ i, ContMDiffOn (𝓡 2) IP ∞ (T i).symm (T i).target) ∧
        (∀ i z, T i z = (ends.lower i.1.1 i.1.2 i.2).chart z) ∧
        (∀ i q t, t ∈ Icc (a - δ) (ends.lowerCut + δ) →
          inner Real v (g (T i (q, t))) = t) ∧
        (∀ t ∈ Icc (a - δ) (ends.lowerCut + δ),
          Injective (fun z : ends.LowerCutIndex × S1 => T z.1 (z.2, t))) ∧
        (∀ i q t, t ∈ Icc a ends.lowerCut → T i (q, t) ∈ ends.endRegion (.inl i)) ∧
        ∃ γ : ends.LowerCutIndex → Real × S1 → (Real ∙ v)ᗮ,
          (∀ i, ContMDiff IT 𝓘(Real, (Real ∙ v)ᗮ) ∞ (γ i)) ∧
          (∀ i t, t ∈ Icc (a - δ) (ends.lowerCut + δ) → ∀ q,
            γ i (t, q) = (Real ∙ v)ᗮ.orthogonalProjectionOnto (g (T i (q, t)))) ∧
          (∀ i t, _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, (Real ∙ v)ᗮ) ∞
            (fun q => γ i (t, q))) ∧
          ∀ t, Injective (fun z : ends.LowerCutIndex × S1 => γ z.1 (t, z.2)) := by
  obtain ⟨a₀, hla, hab, hcenters⟩ := exists_common_strict_upper_bound
    (fun i : ends.LowerCutIndex => i.1.1.center) ends.lower_lt (fun i => i.2)
  obtain ⟨r, hr, γ₀, hγ₀, hγeq, hphysical, hemb, hinj⟩ :=
    ends.exists_lower_terminal_projected_slice_family hg hv
  let A (i : ends.LowerCutIndex) := ends.lower i.1.1 i.1.2 i.2
  have hs (i : ends.LowerCutIndex) (q : S1) : (q, ends.lowerCut) ∈ (A i).chart.source := by
    rw [(A i).source]
    exact ⟨mem_univ _, by linarith [(A i).delta_pos, ends.lower_lt],
      by linarith [(A i).delta_pos]⟩
  obtain ⟨η, hη, hsource, hjoint⟩ := Saddle.Caps.exists_jointly_injective_chart_slices
    (fun i => (A i).chart) hs ends.lowerCutCircle_joint_injective
  let s := min r (min η (ends.lowerCut - a₀))
  have hsp : 0 < s := lt_min hr (lt_min hη (sub_pos.mpr hab))
  have hsr : s ≤ r := min_le_left _ _
  have hsη : s ≤ η := (min_le_right _ _).trans (min_le_left _ _)
  have hsg : s ≤ ends.lowerCut - a₀ := (min_le_right _ _).trans (min_le_right _ _)
  let a := ends.lowerCut - s / 2
  let δ := s / 8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hgap : a₀ < a - δ := by dsimp [a, δ]; linarith
  have hwindow (t : Real) (ht : t ∈ Icc (a - δ) (ends.lowerCut + δ)) :
      t - ends.lowerCut ∈ Icc (-r) r ∧ t ∈ Icc (ends.lowerCut - η) (ends.lowerCut + η) := by
    dsimp [a, δ] at ht
    constructor <;> constructor <;> linarith [ht.1, ht.2]
  let U : Set (S1 × Real) := univ ×ˢ Ioo (a - δ) (ends.lowerCut + δ)
  have hUs (i : ends.LowerCutIndex) : U ⊆ (A i).chart.source := by
    rintro ⟨q, t⟩ ⟨_, ht⟩
    exact hsource i ⟨mem_univ _, (hwindow t ⟨ht.1.le, ht.2.le⟩).2⟩
  let T (i : ends.LowerCutIndex) := (A i).chart.restrOpen U (isOpen_univ.prod isOpen_Ioo)
  let γ (i : ends.LowerCutIndex) (z : Real × S1) := γ₀ i (z.1 - ends.lowerCut, z.2)
  refine ⟨a, δ, hδ, hla.trans hgap, ?_, fun i => (hcenters i).trans hgap,
    T, fun i => inter_eq_right.mpr (hUs i),
    fun i => (A i).smooth.mono inter_subset_left,
    fun i => (A i).symm_smooth.mono inter_subset_left, fun _ _ => rfl, ?_, ?_, ?_,
    γ, ?_, ?_, ?_, ?_⟩
  · dsimp [a, δ]
    linarith
  · intro i q t ht
    change inner Real v (g ((ends.lower i.1.1 i.1.2 i.2).chart (q, t))) = t
    simpa only [add_sub_cancel] using hphysical i (t - ends.lowerCut) (hwindow t ht).1 q
  · intro t ht
    exact hjoint t (hwindow t ht).2
  · intro i q t ht
    exact mem_image_of_mem (A i).chart ⟨mem_univ _,
      ((hcenters i).trans hgap).le.trans (by linarith [ht.1]), ht.2⟩
  · intro i
    exact (hγ₀ i).comp ((contMDiff_fst.sub contMDiff_const).prodMk contMDiff_snd)
  · intro i t ht q
    change γ₀ i (t - ends.lowerCut, q) = (Real ∙ v)ᗮ.orthogonalProjectionOnto
      (g ((ends.lower i.1.1 i.1.2 i.2).chart (q, t)))
    simpa only [add_sub_cancel] using hγeq i (t - ends.lowerCut) (hwindow t ht).1 q
  · intro i t
    exact hemb i (t - ends.lowerCut)
  · intro t
    exact hinj (t - ends.lowerCut)

theorem exists_upper_common_physical_annuli
    (ends : AnnularEndFamily v g B C)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g) (hv : ‖v‖ = 1) :
    ∃ b δ : Real, 0 < δ ∧ b + δ < ends.upperBound ∧
      ends.upperCut + δ < b - δ ∧
      (∀ i : ends.UpperCutIndex, b + δ < i.1.1.center) ∧
      ∃ T : ends.UpperCutIndex → OpenPartialHomeomorph (S1 × Real) S2,
        (∀ i, (T i).source = univ ×ˢ Ioo (ends.upperCut - δ) (b + δ)) ∧
        (∀ i, ContMDiffOn IP (𝓡 2) ∞ (T i) (T i).source) ∧
        (∀ i, ContMDiffOn (𝓡 2) IP ∞ (T i).symm (T i).target) ∧
        (∀ i z, T i z = (ends.upper i.1.1 i.1.2 i.2).chart z) ∧
        (∀ i q t, t ∈ Icc (ends.upperCut - δ) (b + δ) →
          inner Real v (g (T i (q, t))) = t) ∧
        (∀ t ∈ Icc (ends.upperCut - δ) (b + δ),
          Injective (fun z : ends.UpperCutIndex × S1 => T z.1 (z.2, t))) ∧
        (∀ i q t, t ∈ Icc ends.upperCut b → T i (q, t) ∈ ends.endRegion (.inr i)) ∧
        ∃ γ : ends.UpperCutIndex → Real × S1 → (Real ∙ v)ᗮ,
          (∀ i, ContMDiff IT 𝓘(Real, (Real ∙ v)ᗮ) ∞ (γ i)) ∧
          (∀ i t, t ∈ Icc (ends.upperCut - δ) (b + δ) → ∀ q,
            γ i (t, q) = (Real ∙ v)ᗮ.orthogonalProjectionOnto (g (T i (q, t)))) ∧
          (∀ i t, _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, (Real ∙ v)ᗮ) ∞
            (fun q => γ i (t, q))) ∧
          ∀ t, Injective (fun z : ends.UpperCutIndex × S1 => γ z.1 (t, z.2)) := by
  obtain ⟨a₀, hla, hab, hcenters⟩ := exists_common_strict_upper_bound
    (fun i : ends.UpperCutIndex => -i.1.1.center) (neg_lt_neg ends.upper_lt)
    (fun i => neg_lt_neg i.2)
  obtain ⟨r, hr, γ₀, hγ₀, hγeq, hphysical, hemb, hinj⟩ :=
    ends.exists_upper_terminal_projected_slice_family hg hv
  let A (i : ends.UpperCutIndex) := ends.upper i.1.1 i.1.2 i.2
  have hs (i : ends.UpperCutIndex) (q : S1) : (q, ends.upperCut) ∈ (A i).chart.source := by
    rw [(A i).source]
    exact ⟨mem_univ _, by linarith [(A i).reflected.delta_pos],
      by linarith [(A i).reflected.delta_pos, ends.upper_lt]⟩
  obtain ⟨η, hη, hsource, hjoint⟩ := Saddle.Caps.exists_jointly_injective_chart_slices
    (fun i => (A i).chart) hs ends.upperCutCircle_joint_injective
  let s := min r (min η (-a₀ - ends.upperCut))
  have hsp : 0 < s := lt_min hr (lt_min hη (by linarith))
  have hsr : s ≤ r := min_le_left _ _
  have hsη : s ≤ η := (min_le_right _ _).trans (min_le_left _ _)
  have hsg : s ≤ -a₀ - ends.upperCut := (min_le_right _ _).trans (min_le_right _ _)
  let b := ends.upperCut + s / 2
  let δ := s / 8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hgap : b + δ < -a₀ := by dsimp [b, δ]; linarith
  have hwindow (t : Real) (ht : t ∈ Icc (ends.upperCut - δ) (b + δ)) :
      t - ends.upperCut ∈ Icc (-r) r ∧ t ∈ Icc (ends.upperCut - η) (ends.upperCut + η) := by
    dsimp [b, δ] at ht
    constructor <;> constructor <;> linarith [ht.1, ht.2]
  let U : Set (S1 × Real) := univ ×ˢ Ioo (ends.upperCut - δ) (b + δ)
  have hUs (i : ends.UpperCutIndex) : U ⊆ (A i).chart.source := by
    rintro ⟨q, t⟩ ⟨_, ht⟩
    exact hsource i ⟨mem_univ _, (hwindow t ⟨ht.1.le, ht.2.le⟩).2⟩
  let T (i : ends.UpperCutIndex) := (A i).chart.restrOpen U (isOpen_univ.prod isOpen_Ioo)
  let γ (i : ends.UpperCutIndex) (z : Real × S1) := γ₀ i (z.1 - ends.upperCut, z.2)
  refine ⟨b, δ, hδ, by linarith, ?_, fun i => by linarith [hcenters i],
    T, fun i => inter_eq_right.mpr (hUs i),
    fun i => (A i).smooth.mono inter_subset_left,
    fun i => (A i).symm_smooth.mono inter_subset_left, fun _ _ => rfl, ?_, ?_, ?_,
    γ, ?_, ?_, ?_, ?_⟩
  · dsimp [b, δ]
    linarith
  · intro i q t ht
    change inner Real v (g ((ends.upper i.1.1 i.1.2 i.2).chart (q, t))) = t
    simpa only [add_sub_cancel] using hphysical i (t - ends.upperCut) (hwindow t ht).1 q
  · intro t ht
    exact hjoint t (hwindow t ht).2
  · intro i q t ht
    change (A i).chart (q, t) ∈ (A i).region
    rw [(A i).region_eq_image]
    exact mem_image_of_mem (A i).chart ⟨mem_univ _, ht.1, by linarith [ht.2, hcenters i]⟩
  · intro i
    exact (hγ₀ i).comp ((contMDiff_fst.sub contMDiff_const).prodMk contMDiff_snd)
  · intro i t ht q
    change γ₀ i (t - ends.upperCut, q) = (Real ∙ v)ᗮ.orthogonalProjectionOnto
      (g ((ends.upper i.1.1 i.1.2 i.2).chart (q, t)))
    simpa only [add_sub_cancel] using hγeq i (t - ends.upperCut) (hwindow t ht).1 q
  · intro i t
    exact hemb i (t - ends.upperCut)
  · intro t
    exact hinj (t - ends.upperCut)

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap.AnnularEndFamily
