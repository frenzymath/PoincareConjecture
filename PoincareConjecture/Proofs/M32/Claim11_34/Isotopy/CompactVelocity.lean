import PoincareConjecture.Proofs.M32.Claim11_34.Isotopy.LocalVelocity
import PoincareConjecture.Proofs.M32.Mathlib.CompactBumpPartition














noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology Bundle BigOperators

universe u

namespace PoincareConjecture.M32

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]






theorem exists_compactly_supported_sphere_velocity
    {F : ℝ × UnitTwoSphere → M}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3) ∞ F)
    (hembed : ∀ t, Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun q => F (t, q)))
    {U : Set M} (hU : IsOpen U) (hFU : ∀ t, range (fun q => F (t, q)) ⊆ U)
    (hleft : ∀ t : ℝ, t ≤ 0 → ∀ q, F (t, q) = F (0, q))
    (hright : ∀ t : ℝ, 1 ≤ t → ∀ q, F (t, q) = F (1, q)) :
    ∃ (K : Set M) (X : ℝ → (x : M) → TangentSpace (𝓡 3) x),
      IsCompact K ∧ K ⊆ U ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3).tangent ∞
        (fun z : ℝ × M => (⟨z.2, X z.1 z.2⟩ : TangentBundle (𝓡 3) M)) ∧
      (∀ t x, x ∉ K → X t x = 0) ∧
      ∀ t q, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 3) (fun τ => F (τ, q)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (F (t, q)))) := by
  classical
  let IP := 𝓘(ℝ, ℝ).prod (𝓡 3)
  have hlocal (z : ℝ × UnitTwoSphere) :=
    exists_smooth_local_sphere_velocity hF hembed hU hFU z.1 z.2
  choose W Y hWo hzW hWU hY hYorbit using hlocal
  let j : ℝ × UnitTwoSphere → ℝ × M := fun z => (z.1, F z)
  let C := j '' (Icc (0 : ℝ) 1 ×ˢ (univ : Set UnitTwoSphere))
  have hC : IsCompact C :=
    (isCompact_Icc.prod isCompact_univ).image (continuous_fst.prodMk hF.continuous)
  have hcover : C ⊆ ⋃ z, W z := by
    rintro _ ⟨z, _, rfl⟩
    exact mem_iUnion.mpr ⟨z, hzW z⟩
  obtain ⟨S, c, V, _, hCV, ρ, hρc, hρW⟩ :=
    exists_finite_bump_partition_of_isCompact (I := IP) hC W hWo hcover
  let K : Set M := ⋃ i : S, Prod.snd '' tsupport (ρ i : ℝ × M → ℝ)
  have hK : IsCompact K := isCompact_iUnion (fun i => (hρc i).image continuous_snd)
  have hKU : K ⊆ U := by
    intro x hx
    obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp hx
    exact (hWU (c i) (hρW i hz)).2
  let X : ℝ → (x : M) → TangentSpace (𝓡 3) x :=
    fun t x => ∑ i : S, ρ i (t, x) • Y (c i) t x

  let Z : S → (z : ℝ × M) → TangentSpace IP z :=
    fun i z => (0, Y (c i) z.1 z.2)
  have htimeZero : ContMDiff IP 𝓘(ℝ, ℝ).tangent ∞
      (fun z : ℝ × M => (⟨z.1, 0⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    (Bundle.contMDiff_zeroSection ℝ (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type)).comp
      contMDiff_fst
  have hZ (i : S) : ContMDiffOn IP IP.tangent ∞
      (fun z => (⟨z, Z i z⟩ : TangentBundle IP (ℝ × M))) (W (c i)) :=
    (contMDiff_equivTangentBundleProd_symm
      (I := 𝓘(ℝ, ℝ)) (M := ℝ) (I' := 𝓡 3) (M' := M)).comp_contMDiffOn
      (htimeZero.contMDiffOn.prodMk (hY (c i)))
  have hweighted (i : S) : ContMDiff IP IP.tangent ∞
      (fun z => (⟨z, ρ i z • Z i z⟩ : TangentBundle IP (ℝ × M))) :=
    (ρ i).contMDiff.contMDiffOn.smul_section_of_tsupport (hWo (c i)) (hρW i) (hZ i)
  have hsum : ContMDiff IP IP.tangent ∞
      (fun z => (⟨z, ∑ i : S, ρ i z • Z i z⟩ : TangentBundle IP (ℝ × M))) :=
    ContMDiff.sum_section (fun i _ => hweighted i)
  have hX : ContMDiff IP (𝓡 3).tangent ∞
      (fun z : ℝ × M => (⟨z.2, X z.1 z.2⟩ : TangentBundle (𝓡 3) M)) := by
    have hh := ((contMDiff_equivTangentBundleProd
      (I := 𝓘(ℝ, ℝ)) (M := ℝ) (I' := 𝓡 3) (M' := M)).comp hsum).snd
    convert hh using 1
    funext z
    simp only [Finset.univ_eq_attach, Function.comp_apply,
      equivTangentBundleProd_apply, TotalSpace.mk_inj]
    change (∑ i : S, ρ i z • (Y (c i) z.1 z.2 : EuclideanSpace ℝ (Fin 3))) =
      (∑ i : S, ρ i z • ((0 : ℝ), (Y (c i) z.1 z.2 : EuclideanSpace ℝ (Fin 3)))).2
    exact (Prod.snd_sum (s := Finset.univ)
      (f := fun i : S => ρ i z • ((0 : ℝ),
        (Y (c i) z.1 z.2 : EuclideanSpace ℝ (Fin 3))))).symm
  have hzero (t : ℝ) (x : M) (hx : x ∉ K) : X t x = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hn : (t, x) ∉ tsupport (ρ i : ℝ × M → ℝ) := by
      intro hi
      exact hx (mem_iUnion.mpr ⟨i, (t, x), hi, rfl⟩)
    rw [image_eq_zero_of_notMem_tsupport hn, zero_smul]
  let v (t : ℝ) (q : UnitTwoSphere) : TangentSpace (𝓡 3) (F (t, q)) :=
    mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun τ => F (τ, q)) t 1
  have hcurve (t : ℝ) (q : UnitTwoSphere) :
      HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 3) (fun τ => F (τ, q)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (v t q)) := by
    have hh : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞ (fun τ => F (τ, q)) :=
      hF.comp (contMDiff_id.prodMk contMDiff_const)
    apply ((hh.mdifferentiable (by simp) t).hasMFDerivAt).congr_mfderiv
    apply ContinuousLinearMap.ext
    intro a
    change ℝ at a
    change mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun τ => F (τ, q)) t a = a • v t q
    simpa only [smul_eq_mul, mul_one] using
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun τ => F (τ, q)) t).map_smul a 1
  have hterm (i : S) (t : ℝ) (q : UnitTwoSphere) (hi : ρ i (t, F (t, q)) ≠ 0) :
      Y (c i) t (F (t, q)) = v t q := by
    have htW := hρW i (subset_tsupport (ρ i) hi)
    have he := hasMFDerivAt_unique (hYorbit (c i) t q htW) (hcurve t q)
    simpa using congrArg (fun L : ℝ →L[ℝ] TangentSpace (𝓡 3) (F (t, q)) => L 1) he
  have hvzero (t : ℝ) (q : UnitTwoSphere) (ht : t ∉ Icc (0 : ℝ) 1) : v t q = 0 := by
    have hconst : ∃ x : M, (fun τ => F (τ, q)) =ᶠ[𝓝 t] (fun _ => x) := by
      by_cases hlt : t < 0
      · refine ⟨F (0, q), ?_⟩
        filter_upwards [Iio_mem_nhds hlt] with τ hτ
        exact hleft τ (le_of_lt hτ) q
      · have hgt : 1 < t := lt_of_not_ge (fun hle => ht ⟨le_of_not_gt hlt, hle⟩)
        refine ⟨F (1, q), ?_⟩
        filter_upwards [Ioi_mem_nhds hgt] with τ hτ
        exact hright τ (le_of_lt hτ) q
    obtain ⟨x, hx⟩ := hconst
    have hc := (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 3) x t).congr_of_eventuallyEq hx
    have he := hasMFDerivAt_unique (hcurve t q) hc
    simpa using congrArg (fun L : ℝ →L[ℝ] TangentSpace (𝓡 3) (F (t, q)) => L 1) he
  refine ⟨K, X, hK, hKU, hX, hzero, ?_⟩
  intro t q
  suffices he : X t (F (t, q)) = v t q by
    rw [he]
    exact hcurve t q
  change (∑ i : S, ρ i (t, F (t, q)) • Y (c i) t (F (t, q))) = v t q
  have hs : (∑ i : S, ρ i (t, F (t, q)) • Y (c i) t (F (t, q))) =
      (∑ i : S, ρ i (t, F (t, q))) • v t q := by
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : ρ i (t, F (t, q)) = 0
    · rw [hi, zero_smul, zero_smul]
    · rw [hterm i t q hi]
  rw [hs]
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · have hmem : (t, F (t, q)) ∈ V := hCV ⟨(t, q), ⟨ht, mem_univ _⟩, rfl⟩
    have hone : (∑ i : S, ρ i (t, F (t, q))) = 1 := by
      simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hmem
    rw [hone, one_smul]
  · rw [hvzero t q ht, smul_zero]

end PoincareConjecture.M32
