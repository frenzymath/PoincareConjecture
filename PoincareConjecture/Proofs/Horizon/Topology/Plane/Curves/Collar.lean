import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.LocalStraightening
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false

open Set
open scoped ContDiff Topology

namespace Poincare.Topology.Plane.Curves

noncomputable def quarterTurn : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv.symm.trans
    (ContinuousLinearEquiv.smulLeft (Units.mk0 Complex.I Complex.I_ne_zero))).trans
      Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv

theorem quarterTurn_apply (v : EuclideanSpace ℝ (Fin 2)) :
    quarterTurn v = Complex.orthonormalBasisOneI.repr
      (Complex.I * Complex.orthonormalBasisOneI.repr.symm v) := rfl

theorem inner_quarterTurn_self (v : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ v (quarterTurn v) = 0 := by
  let E := Complex.orthonormalBasisOneI.repr
  change inner ℝ v (E (Complex.I * E.symm v)) = 0
  conv_lhs => lhs; rw [← E.apply_symm_apply v]
  rw [E.inner_map_map]
  exact real_inner_I_smul_self ℂ (E.symm v)

noncomputable def normalStrip (f : ℝ → EuclideanSpace ℝ (Fin 2))
    (q : ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) :=
  f q.1 + q.2 • quarterTurn (deriv f q.1)

@[simp] theorem normalStrip_axis (f : ℝ → EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    normalStrip f (t, 0) = f t := by simp [normalStrip]

theorem contDiff_normalStrip {f : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (normalStrip f) := by
  exact (hf.comp contDiff_fst).add
    (contDiff_snd.smul ((quarterTurn.contDiff.comp
      (contDiff_infty_iff_deriv.mp hf).2).comp contDiff_fst))

theorem exists_strictFDerivAt_normalStrip_axis
    {f : ℝ → EuclideanSpace ℝ (Fin 2)} (hf : ContDiff ℝ ∞ f)
    {t : ℝ} (hregular : deriv f t ≠ 0) :
    ∃ L : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2),
      (∀ q : ℝ × ℝ, L q = q.1 • deriv f t + q.2 • quarterTurn (deriv f t)) ∧
      HasStrictFDerivAt (normalStrip f) (L : (ℝ × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 2))
        (t, 0) := by
  let E := Complex.orthonormalBasisOneI.repr
  let z : ℂ := E.symm (deriv f t)
  have hz : z ≠ 0 := by
    intro h
    apply hregular
    have := congrArg E h
    simpa [z] using this
  have hzmap : E z = deriv f t := E.apply_symm_apply _
  let L : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    (Complex.equivRealProdCLM.symm.trans
      (ContinuousLinearEquiv.smulLeft (Units.mk0 z hz))).trans E.toContinuousLinearEquiv
  have hL (q : ℝ × ℝ) :
      L q = q.1 • deriv f t + q.2 • quarterTurn (deriv f t) := by
    change E (z * Complex.equivRealProdCLM.symm q) = _
    have hmul : z * Complex.equivRealProdCLM.symm q =
        q.1 • z + q.2 • (Complex.I * z) := by
      rw [Complex.equivRealProdCLM_symm_apply]
      simp only [Complex.real_smul]
      ring
    rw [hmul, map_add, map_smul, map_smul, hzmap]
    rfl
  let n : ℝ → EuclideanSpace ℝ (Fin 2) := fun u => quarterTurn (deriv f u)
  have hn : ContDiff ℝ ∞ n := quarterTurn.contDiff.comp (contDiff_infty_iff_deriv.mp hf).2
  refine ⟨L, hL, ?_⟩
  convert! ((hf.hasStrictDerivAt (by simp)).hasStrictFDerivAt.comp (t, 0)
    hasStrictFDerivAt_fst).add
    ((hasStrictFDerivAt_snd (𝕜 := ℝ) (p := (t, (0 : ℝ)))).smul
      ((hn.hasStrictFDerivAt (by simp)).comp (t, 0) hasStrictFDerivAt_fst)) using 1
  apply ContinuousLinearMap.ext
  intro q
  simpa [n] using hL q

theorem exists_local_normal_collar
    {f : ℝ → EuclideanSpace ℝ (Fin 2)} (hf : ContDiff ℝ ∞ f)
    {t : ℝ} (hregular : deriv f t ≠ 0) :
    ∃ F : OpenPartialHomeomorph (ℝ × ℝ) (EuclideanSpace ℝ (Fin 2)),
      (t, 0) ∈ F.source ∧ (∀ q, F q = normalStrip f q) ∧
      ContDiffAt ℝ ∞ F (t, 0) ∧ ContDiffAt ℝ ∞ F.symm (f t) := by
  obtain ⟨L, _, hd⟩ := exists_strictFDerivAt_normalStrip_axis hf hregular
  let F := hd.toOpenPartialHomeomorph (normalStrip f)
  have hp : (t, 0) ∈ F.source := hd.mem_toOpenPartialHomeomorph_source
  have hbase : F (t, 0) = f t := normalStrip_axis f t
  have hinverse : F.symm (f t) = (t, 0) := by
    rw [← hbase]
    exact F.left_inv hp
  have hcont : ContDiffAt ℝ ∞ F (t, 0) := (contDiff_normalStrip hf).contDiffAt
  refine ⟨F, hp, fun _ => rfl, hcont, ?_⟩
  apply F.contDiffAt_symm (hbase ▸ F.map_source hp)
  · rw [hinverse]
    exact hd.hasFDerivAt
  · rw [hinverse]
    exact hcont

theorem exists_normal_collar
    {f : ℝ → EuclideanSpace ℝ (Fin 2)} (hf : ContDiff ℝ ∞ f)
    {a b : ℝ} (hinj : InjOn f (Icc a b))
    (hregular : ∀ t ∈ Icc a b, deriv f t ≠ 0) :
    ∃ ε > 0,
      InjOn (normalStrip f) (Icc a b ×ˢ Ioo (-ε) ε) ∧
      ContDiffOn ℝ ∞ (normalStrip f) (Icc a b ×ˢ Ioo (-ε) ε) ∧
      ∀ t ∈ Icc a b, ∃ L : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2),
        HasStrictFDerivAt (normalStrip f)
          (L : (ℝ × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 2)) (t, 0) := by
  have haxis : InjOn (normalStrip f) (Icc a b ×ˢ ({0} : Set ℝ)) := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩ ⟨u, v⟩ ⟨hu, hv⟩ heq
    have hs0 : s = 0 := hs
    have hv0 : v = 0 := hv
    subst s
    subst v
    exact Prod.ext (hinj ht hu (by simpa only [normalStrip_axis] using heq)) rfl
  have hloc : ∀ q ∈ Icc a b ×ˢ ({0} : Set ℝ),
      ∃ W ∈ 𝓝 q, InjOn (normalStrip f) W := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    obtain ⟨F, hp, hF, _, _⟩ := exists_local_normal_collar hf (hregular t ht)
    refine ⟨F.source, F.open_source.mem_nhds hp, ?_⟩
    intro q hq z hz heq
    apply F.injOn hq hz
    simpa only [hF] using heq
  obtain ⟨W, hW, hWinj⟩ := haxis.exists_mem_nhdsSet
    (isCompact_Icc.prod isCompact_singleton)
    (fun _ _ => (contDiff_normalStrip hf).continuous.continuousAt) hloc
  rw [isCompact_Icc.nhdsSet_prod_eq isCompact_singleton, nhdsSet_singleton] at hW
  obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_prod_iff.mp hW
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp hV
  have hstrip : Icc a b ×ˢ Ioo (-ε) ε ⊆ W := by
    apply (prod_mono (subset_of_mem_nhdsSet hU) ?_).trans hUV
    simpa only [Real.ball_eq_Ioo, zero_sub, zero_add] using hεV
  refine ⟨ε, hε, hWinj.mono hstrip, (contDiff_normalStrip hf).contDiffOn, ?_⟩
  intro t ht
  obtain ⟨L, _, hd⟩ := exists_strictFDerivAt_normalStrip_axis hf (hregular t ht)
  exact ⟨L, hd⟩

theorem exists_normal_collar_coordinates
    {f : ℝ → EuclideanSpace ℝ (Fin 2)} (hf : ContDiff ℝ ∞ f)
    {a b : ℝ} (hinj : InjOn f (Icc a b))
    (hregular : ∀ t ∈ Icc a b, deriv f t ≠ 0) :
    ∃ ε > 0, ∃ F : OpenPartialHomeomorph (ℝ × ℝ) (EuclideanSpace ℝ (Fin 2)),
      F.source ∈ 𝓝ˢ (Icc a b ×ˢ ({0} : Set ℝ)) ∧
      Icc a b ×ˢ Ioo (-ε) ε ⊆ F.source ∧
      (∀ q, F q = normalStrip f q) ∧
      ContDiffOn ℝ ∞ F F.source ∧ ContDiffOn ℝ ∞ F.symm F.target ∧
      ∀ q ∈ F.source, ∃ L : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2),
        HasStrictFDerivAt F (L : (ℝ × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 2)) q := by
  have hG := contDiff_normalStrip hf
  let R := (fderiv ℝ (normalStrip f)) ⁻¹'
    range (fun L : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) =>
      (L : (ℝ × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 2)))
  have hRopen : IsOpen R :=
    ContinuousLinearEquiv.isOpen.preimage (hG.continuous_fderiv (by simp))
  have hRaxis : Icc a b ×ˢ ({0} : Set ℝ) ⊆ R := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    obtain ⟨L, _, hd⟩ := exists_strictFDerivAt_normalStrip_axis hf (hregular t ht)
    exact ⟨L, hd.hasFDerivAt.fderiv.symm⟩
  have haxis : InjOn (normalStrip f) (Icc a b ×ˢ ({0} : Set ℝ)) := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩ ⟨u, v⟩ ⟨hu, hv⟩ heq
    have hs0 : s = 0 := hs
    have hv0 : v = 0 := hv
    subst s
    subst v
    exact Prod.ext (hinj ht hu (by simpa only [normalStrip_axis] using heq)) rfl
  have hloc : ∀ q ∈ Icc a b ×ˢ ({0} : Set ℝ),
      ∃ W ∈ 𝓝 q, InjOn (normalStrip f) W := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    obtain ⟨F, hp, hF, _, _⟩ := exists_local_normal_collar hf (hregular t ht)
    refine ⟨F.source, F.open_source.mem_nhds hp, ?_⟩
    intro q hq z hz heq
    apply F.injOn hq hz
    simpa only [hF] using heq
  obtain ⟨V, hVopen, hVaxis, hVinj⟩ := haxis.exists_isOpen_superset
    (isCompact_Icc.prod isCompact_singleton) (fun _ _ => hG.continuous.continuousAt) hloc
  let W := V ∩ R
  have hWopen : IsOpen W := hVopen.inter hRopen
  have hWaxis : Icc a b ×ˢ ({0} : Set ℝ) ⊆ W :=
    subset_inter hVaxis hRaxis
  have hWinj : InjOn (normalStrip f) W := hVinj.mono inter_subset_left
  have hderiv (q : ℝ × ℝ) (hq : q ∈ W) :
      ∃ L : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2),
        HasStrictFDerivAt (normalStrip f)
          (L : (ℝ × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 2)) q := by
    obtain ⟨L, hL⟩ := hq.2
    refine ⟨L, ?_⟩
    convert! hG.hasStrictFDerivAt (x := q) (by simp) using 1
  have hopenmap : IsOpenMap (W.domRestrict (normalStrip f)) := by
    apply isOpenMap_iff_nhds_le.mpr
    intro q
    obtain ⟨L, hd⟩ := hderiv q q.property
    change 𝓝 (normalStrip f q) ≤ Filter.map (normalStrip f ∘ Subtype.val) (𝓝 q)
    rw [← Filter.map_map, hWopen.isOpenEmbedding_subtypeVal.map_nhds_eq,
      hd.map_nhds_eq_of_equiv]
  let F := OpenPartialHomeomorph.ofContinuousOpenRestrict
    (hWinj.toPartialEquiv (normalStrip f) W) hG.continuous.continuousOn hopenmap hWopen
  have hWnhds : W ∈ 𝓝ˢ (Icc a b ×ˢ ({0} : Set ℝ)) := hWopen.mem_nhdsSet.mpr hWaxis
  have hprod := hWnhds
  rw [isCompact_Icc.nhdsSet_prod_eq isCompact_singleton, nhdsSet_singleton] at hprod
  obtain ⟨U, hU, T, hT, hUT⟩ := Filter.mem_prod_iff.mp hprod
  obtain ⟨ε, hε, hεT⟩ := Metric.mem_nhds_iff.mp hT
  have hstrip : Icc a b ×ˢ Ioo (-ε) ε ⊆ W := by
    apply (prod_mono (subset_of_mem_nhdsSet hU) ?_).trans hUT
    simpa only [Real.ball_eq_Ioo, zero_sub, zero_add] using hεT
  refine ⟨ε, hε, F, hWnhds, hstrip, fun _ => rfl, hG.contDiffOn, ?_, hderiv⟩
  intro y hy
  obtain ⟨L, hd⟩ := hderiv (F.symm y) (F.map_target hy)
  exact (F.contDiffAt_symm hy hd.hasFDerivAt hG.contDiffAt).contDiffWithinAt

end Poincare.Topology.Plane.Curves
