import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SphereEmbeddingRetraction
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CompactDisplacement
import Mathlib.Geometry.Manifold.PartitionOfUnity












set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M28

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

private theorem contDiff_sphere_displacement_term
    {F : ℝ × UnitTwoSphere → E₃}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E₃) ∞ F)
    {V : Set E₃} (hV : IsOpen V) {r : E₃ → UnitTwoSphere}
    (hr : ContMDiffOn 𝓘(ℝ, E₃) (𝓡 2) ∞ r V)
    {ρ : E₃ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρV : tsupport ρ ⊆ V) (t₀ : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × E₃ =>
      ρ p.2 • (F (p.1, r p.2) - F (t₀, r p.2))) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p.2 ∈ tsupport ρ
  · have hrp : ContMDiffAt 𝓘(ℝ, ℝ × E₃) (𝓡 2) ∞ (fun y => r y.2) p :=
      (hr.contMDiffAt (hV.mem_nhds (hρV hp))).comp p
        (contDiff_snd.contMDiff.contMDiffAt)
    have hFt : ContMDiffAt 𝓘(ℝ, ℝ × E₃) 𝓘(ℝ, E₃) ∞
        (fun y : ℝ × E₃ => F (y.1, r y.2)) p :=
      hF.contMDiffAt.comp p (contDiff_fst.contMDiff.contMDiffAt.prodMk hrp)
    have hF₀ : ContMDiffAt 𝓘(ℝ, ℝ × E₃) 𝓘(ℝ, E₃) ∞
        (fun y : ℝ × E₃ => F (t₀, r y.2)) p :=
      hF.contMDiffAt.comp p (contMDiffAt_const.prodMk hrp)
    exact (hρ.comp contDiff_snd).contDiffAt.smul (hFt.contDiffAt.sub hF₀.contDiffAt)
  · have hz : (fun y : ℝ × E₃ => ρ y.2) =ᶠ[𝓝 p] 0 :=
      (notMem_tsupport_iff_eventuallyEq.mp hp).comp_tendsto continuous_snd.continuousAt
    apply (contDiffAt_const (c := (0 : E₃))).congr_of_eventuallyEq
    filter_upwards [hz] with y hy
    change ρ y.2 = 0 at hy
    simp only [hy, zero_smul]




theorem exists_compact_sphere_displacement
    {F : ℝ × UnitTwoSphere → E₃}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E₃) ∞ F)
    (t₀ : ℝ) (U : Set E₃)
    (hlocal : ∀ q : UnitTwoSphere, ∃ (V : Set E₃) (r : E₃ → UnitTwoSphere),
      IsOpen V ∧ F (t₀, q) ∈ V ∧ V ⊆ U ∧
      ContMDiffOn 𝓘(ℝ, E₃) (𝓡 2) ∞ r V ∧
      ∀ z : UnitTwoSphere, F (t₀, z) ∈ V → r (F (t₀, z)) = z) :
    ∃ (D : ℝ × E₃ → E₃) (K : Set E₃),
      ContDiff ℝ ∞ D ∧ IsCompact K ∧ K ⊆ U ∧
      (∀ t : ℝ, tsupport (fun x => D (t, x)) ⊆ K) ∧
      (∀ x : E₃, D (t₀, x) = 0) ∧
      ∀ (t : ℝ) (q : UnitTwoSphere), F (t₀, q) + D (t, F (t₀, q)) = F (t, q) := by
  classical
  choose V r hVo hVq hVU hr hret using hlocal
  have hshrink (q : UnitTwoSphere) : ∃ W : Set E₃,
      IsOpen W ∧ F (t₀, q) ∈ W ∧ closure W ⊆ V q ∧ IsCompact (closure W) := by
    obtain ⟨W, hWo, hqW, hWV, hWc⟩ :=
      exists_open_between_and_isCompact_closure isCompact_singleton (hVo q)
        (singleton_subset_iff.mpr (hVq q))
    exact ⟨W, hWo, hqW (mem_singleton _), hWV, hWc⟩
  choose W hWo hWq hWV hWc using hshrink
  have hF₀ : ContMDiff (𝓡 2) 𝓘(ℝ, E₃) ∞ (fun q => F (t₀, q)) :=
    hF.comp (contMDiff_const.prodMk contMDiff_id)
  have himage : IsCompact (range (fun q : UnitTwoSphere => F (t₀, q))) := by
    simpa only [image_univ] using isCompact_univ.image hF₀.continuous
  obtain ⟨s, hs⟩ := himage.elim_finite_subcover W hWo (by
    rintro x ⟨q, rfl⟩
    exact mem_iUnion.mpr ⟨q, hWq q⟩)
  let J : Type := {q : UnitTwoSphere // q ∈ s}
  let W' : J → Set E₃ := fun j => W j.1
  have hcover : range (fun q : UnitTwoSphere => F (t₀, q)) ⊆ ⋃ j : J, W' j := by
    intro x hx
    obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion.mpr ⟨⟨q, hq⟩, hxq⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, E₃)) himage.isClosed W' (fun j => hWo j.1) hcover
  let K : Set E₃ := ⋃ j : J, closure (W' j)
  have hK : IsCompact K := isCompact_iUnion (fun j : J => hWc j.1)
  have hKU : K ⊆ U := by
    intro x hx
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
    exact hVU j.1 (hWV j.1 hxj)
  let D : ℝ × E₃ → E₃ := fun p =>
    ∑ j : J, ρ j p.2 • (F (p.1, r j.1 p.2) - F (t₀, r j.1 p.2))
  have hD : ContDiff ℝ ∞ D := by
    apply ContDiff.sum
    intro j _
    exact contDiff_sphere_displacement_term hF (hVo j.1) (hr j.1)
      (ρ j).contMDiff.contDiff
      (fun x hx => hWV j.1 (subset_closure (hρ j hx))) t₀
  have hsupport (t : ℝ) : tsupport (fun x => D (t, x)) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hxK
    have hz (j : J) : ρ j x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hxρ
      exact hxK (mem_iUnion.mpr ⟨j, subset_closure (hρ j hxρ)⟩)
    exact hx (by simp [D, hz])
  have hzero (x : E₃) : D (t₀, x) = 0 := by simp [D]
  refine ⟨D, K, hD, hK, hKU, hsupport, hzero, ?_⟩
  intro t q
  have hsum : (∑ j : J, ρ j (F (t₀, q))) = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_range_self q)
  have hterm (j : J) :
      ρ j (F (t₀, q)) •
        (F (t, r j.1 (F (t₀, q))) - F (t₀, r j.1 (F (t₀, q)))) =
      ρ j (F (t₀, q)) • (F (t, q) - F (t₀, q)) := by
    by_cases hz : ρ j (F (t₀, q)) = 0
    · simp only [hz, zero_smul]
    · have hxρ : F (t₀, q) ∈ tsupport (ρ j) := subset_closure hz
      rw [hret j.1 q (hWV j.1 (subset_closure (hρ j hxρ)))]
  change F (t₀, q) +
    ∑ j : J, ρ j (F (t₀, q)) •
      (F (t, r j.1 (F (t₀, q))) - F (t₀, r j.1 (F (t₀, q)))) = _
  simp_rw [hterm]
  rw [← Finset.sum_smul, hsum, one_smul]
  abel

end PoincareConjecture.M28
