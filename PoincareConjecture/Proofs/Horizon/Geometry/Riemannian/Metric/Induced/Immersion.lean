import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Hom

set_option backward.isDefEq.respectTransparency false

namespace PoincareConjecture.RiemannianMetric.Induced

open Bornology Bundle Manifold ContinuousLinearMap
open scoped Manifold ContDiff Topology

private theorem isVonNBounded_of_posDef {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (q : F →L[ℝ] F →L[ℝ] ℝ) (hpos : ∀ v : F, v ≠ 0 → 0 < q v v) :
    Bornology.IsVonNBounded ℝ {v : F | q v v < 1} := by
  rcases subsingleton_or_nontrivial F with hs | hn
  · exact Set.Finite.isVonNBounded (𝕜 := ℝ) (Set.toFinite _)
  have hcompact : IsCompact (Metric.sphere (0 : F) 1) := isCompact_sphere 0 1
  have hne : (Metric.sphere (0 : F) 1).Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
  have hcont : Continuous fun v : F => q v v := q.continuous.clm_apply continuous_id
  obtain ⟨v₀, hv₀mem, hv₀min⟩ := hcompact.exists_isMinOn hne hcont.continuousOn
  set c := q v₀ v₀ with hc_def
  have hv₀ne : v₀ ≠ 0 := by
    intro h; rw [mem_sphere_iff_norm, sub_zero, h, norm_zero] at hv₀mem; norm_num at hv₀mem
  have hc : 0 < c := hpos v₀ hv₀ne
  have hcoer : ∀ v : F, c * ‖v‖ ^ 2 ≤ q v v := by
    intro v; rcases eq_or_ne v 0 with rfl | hv
    · simp
    · have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      set u := ‖v‖⁻¹ • v with hu
      have hmem : u ∈ Metric.sphere (0 : F) 1 := by
        rw [mem_sphere_iff_norm, sub_zero, hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnv]
      have hqu : c ≤ q u u := hv₀min hmem
      have hexp : q v v = ‖v‖ ^ 2 * q u u := by
        rw [hu]; simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]; field_simp
      rw [hexp]; nlinarith [hqu, sq_nonneg ‖v‖]
  apply Bornology.IsVonNBounded.subset _ (NormedSpace.isVonNBounded_ball ℝ F (Real.sqrt (1 / c) + 1))
  intro v hv; simp only [Set.mem_setOf_eq] at hv; rw [Metric.mem_ball, dist_zero_right]
  have h1 : c * ‖v‖ ^ 2 < 1 := lt_of_le_of_lt (hcoer v) hv
  have h2 : ‖v‖ ^ 2 < 1 / c := by rw [lt_div_iff₀ hc]; linarith [mul_comm c (‖v‖^2)]
  have h3 : ‖v‖ < Real.sqrt (1 / c) := by
    rw [show ‖v‖ = Real.sqrt (‖v‖^2) by rw [Real.sqrt_sq (norm_nonneg _)]]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) h2
  linarith [Real.sqrt_nonneg (1/c)]

section Pullback

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

noncomputable def pullbackFormOf
    (b : ∀ y : M', TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] ℝ) (F : M → M') (p : M) :
    TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ :=
  let A : E →L[ℝ] E' := mfderiv I I' F p
  let B : E' →L[ℝ] E' →L[ℝ] ℝ := b (F p)
  (B.bilinearComp A A : E →L[ℝ] E →L[ℝ] ℝ)

omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
@[simp] theorem pullbackFormOf_apply
    (b : ∀ y : M', TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] ℝ) (F : M → M') (p : M)
    (v w : TangentSpace I p) :
    pullbackFormOf b F p v w = b (F p) (mfderiv I I' F p v) (mfderiv I I' F p w) :=
  rfl

noncomputable def pullbackForm (g' : Bundle.ContMDiffRiemannianMetric I' ∞ E' (TangentSpace I' : M' → Type _)) (F : M → M') (p : M) :
    TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ :=
  pullbackFormOf (fun y => g'.inner y) F p

omit [IsManifold I ∞ M] in
@[simp] theorem pullbackForm_apply (g' : Bundle.ContMDiffRiemannianMetric I' ∞ E' (TangentSpace I' : M' → Type _)) (F : M → M') (p : M)
    (v w : TangentSpace I p) :
    pullbackForm g' F p v w = g'.inner (F p) (mfderiv I I' F p v) (mfderiv I I' F p w) :=
  rfl

omit [IsManifold I ∞ M] in

theorem pullbackForm_symm (g' : Bundle.ContMDiffRiemannianMetric I' ∞ E' (TangentSpace I' : M' → Type _)) (F : M → M') (p : M)
    (v w : TangentSpace I p) :
    pullbackForm g' F p v w = pullbackForm g' F p w v := by
  simp only [pullbackForm_apply]
  exact g'.symm _ _ _

omit [IsManifold I ∞ M] in

theorem pullbackForm_posDef_iff_immersion (g' : Bundle.ContMDiffRiemannianMetric I' ∞ E' (TangentSpace I' : M' → Type _)) (F : M → M') :
    (∀ (p : M) (v : TangentSpace I p), v ≠ 0 → 0 < pullbackForm g' F p v v) ↔
      ∀ p : M, Function.Injective (mfderiv I I' F p) := by
  constructor
  ·
    intro hpos p
    rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra hv0
    have := hpos p v hv0
    rw [pullbackForm_apply, hv] at this
    simp at this
  ·
    intro himm p v hv
    rw [pullbackForm_apply]
    exact g'.pos _ _ fun h => hv (himm p (by rw [h, map_zero]))

noncomputable def bilinearCompOf
    (b : ∀ y : M', TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] ℝ) {F : M → M'}
    (A : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I' (F x)) (p : M) :
    TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ :=
  let A' : E →L[ℝ] E' := A p
  let B : E' →L[ℝ] E' →L[ℝ] ℝ := b (F p)
  (B.bilinearComp A' A' : E →L[ℝ] E →L[ℝ] ℝ)

omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
@[simp] theorem bilinearCompOf_apply
    (b : ∀ y : M', TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] ℝ) {F : M → M'}
    (A : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I' (F x)) (p : M)
    (v w : TangentSpace I p) :
    bilinearCompOf b A p v w = b (F p) (A p v) (A p w) :=
  rfl

omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in

theorem pullbackFormOf_eq_bilinearCompOf
    (b : ∀ y : M', TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] ℝ) (F : M → M') (p : M) :
    pullbackFormOf b F p = bilinearCompOf b (fun x => mfderiv I I' F x) p :=
  rfl

theorem contMDiffAt_bilinearCompOf
    (b : ∀ y : M', TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] ℝ)
    (hb : ContMDiff I' (I'.prod 𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ)) ∞
      (fun y ↦ (⟨y, b y⟩ :
        Bundle.TotalSpace (E' →L[ℝ] E' →L[ℝ] ℝ)
          (fun y ↦ TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] ℝ))))
    {F : M → M'} {x₀ : M} (hF : ContMDiffAt I I' ∞ F x₀)
    (A : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I' (F x))
    (hA : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E') ∞ (inTangentCoordinates I I' id F A x₀) x₀) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x ↦ (⟨x, bilinearCompOf b A x⟩ :
        Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))) x₀ := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  set sT := trivializationAt E (TangentSpace I) x₀ with hsT
  set tT := trivializationAt E' (TangentSpace I' : M' → Type _) (F x₀) with htT
  have hx₀ : x₀ ∈ sT.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hfx₀ : F x₀ ∈ tT.baseSet := mem_baseSet_trivializationAt E' (TangentSpace I' : M' → Type _) (F x₀)
  set D : M → (E →L[ℝ] E') := inTangentCoordinates I I' id F A x₀ with hD
  set G : M' → (E' →L[ℝ] E' →L[ℝ] ℝ) := fun y =>
    ContinuousLinearMap.inCoordinates E' (TangentSpace I' : M' → Type _) (E' →L[ℝ] ℝ)
      (fun y => TangentSpace I' y →L[ℝ] ℝ) (F x₀) y (F x₀) y (b y) with hG
  have hGsmooth : ContMDiffAt I' 𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ) ∞ G (F x₀) :=
    ((contMDiffAt_hom_bundle _).mp hb.contMDiffAt).2
  have hΨ : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun x => ((D x).precomp ℝ).comp ((G (F x)).comp (D x))) x₀ := by
    have h1 : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E' →L[ℝ] ℝ) ∞
        (fun x => (G (F x)).comp (D x)) x₀ :=
      (hGsmooth.comp x₀ hF).clm_comp hA
    exact (ContMDiffAt.clm_precomp (F₃ := ℝ) hA).clm_comp h1
  refine hΨ.congr_of_eventuallyEq ?_
  have hUs : {x | x ∈ sT.baseSet} ∈ 𝓝 x₀ := sT.open_baseSet.mem_nhds hx₀
  have hUt : {x | F x ∈ tT.baseSet} ∈ 𝓝 x₀ :=
    hF.continuousAt (tT.open_baseSet.mem_nhds hfx₀)
  filter_upwards [hUs, hUt] with x hx hfx
  refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b' => ?_
  have hRHS : (((ContinuousLinearMap.precomp ℝ (D x)).comp ((G (F x)).comp (D x))) a) b'
      = G (F x) (D x a) (D x b') := rfl

  have hkey : ∀ u : E, tT.symm (F x) (D x u) = A x (sT.symm x u) := by
    intro u
    have hDu : D x u = tT.continuousLinearEquivAt ℝ (F x) hfx
        (A x ((sT.continuousLinearEquivAt ℝ x hx).symm u)) := by
      rw [hD]
      simp only [inTangentCoordinates, id_eq]
      rw [ContinuousLinearMap.inCoordinates_eq hx hfx]
      rfl
    have hcoeT : (tT.symm (F x) : E' → TangentSpace I' (F x))
        = ⇑(tT.continuousLinearEquivAt ℝ (F x) hfx).symm := rfl
    have hcoeS : (sT.symm x : E → TangentSpace I x)
        = ⇑(sT.continuousLinearEquivAt ℝ x hx).symm := rfl
    rw [hDu, hcoeT, ContinuousLinearEquiv.symm_apply_apply, hcoeS]
  rw [hRHS, hG]
  have htrivM' :
      trivializationAt ℝ (Bundle.Trivial M' ℝ) (F x₀) = Bundle.Trivial.trivialization M' ℝ :=
    Bundle.Trivial.eq_trivialization M' ℝ _
  have htrivM : trivializationAt ℝ (Bundle.Trivial M ℝ) x₀ = Bundle.Trivial.trivialization M ℝ :=
    Bundle.Trivial.eq_trivialization M ℝ _
  rw [inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial M' ℝ) hfx hfx (by simp)]
  rw [inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial M ℝ) hx hx (by simp)]
  simp only [htrivM', htrivM, Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_coe, id_eq,
    bilinearCompOf_apply, ← htT, ← hsT, hkey]

theorem contMDiff_pullbackFormOf
    (b : ∀ y : M', TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] ℝ)
    (hb : ContMDiff I' (I'.prod 𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ)) ∞
      (fun y ↦ (⟨y, b y⟩ :
        Bundle.TotalSpace (E' →L[ℝ] E' →L[ℝ] ℝ)
          (fun y ↦ TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] ℝ))))
    {F : M → M'} (hF : ContMDiff I I' ∞ F) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x ↦ (⟨x, pullbackFormOf b F x⟩ :
        Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))) := fun x₀ =>
  contMDiffAt_bilinearCompOf b hb hF.contMDiffAt (fun x => mfderiv I I' F x)
    (hF.contMDiffAt.mfderiv_const (by simp))

theorem pullbackForm_contMDiff (g' : Bundle.ContMDiffRiemannianMetric I' ∞ E' (TangentSpace I' : M' → Type _)) {F : M → M'}
    (hF : ContMDiff I I' ∞ F) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x ↦ (⟨x, pullbackForm g' F x⟩ :
        Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))) :=
  contMDiff_pullbackFormOf (fun y => g'.inner y) g'.contMDiff hF

variable [FiniteDimensional ℝ E]

noncomputable def pullbackMetric (g' : Bundle.ContMDiffRiemannianMetric I' ∞ E' (TangentSpace I' : M' → Type _)) (F : M → M')
    (hF : ContMDiff I I' ∞ F) (himm : ∀ p : M, Function.Injective (mfderiv I I' F p)) :
    Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _) where
  inner p := pullbackForm g' F p
  symm p v w := pullbackForm_symm g' F p v w
  pos p v hv := (pullbackForm_posDef_iff_immersion g' F).mpr himm p v hv
  isVonNBounded p := by
    refine isVonNBounded_of_posDef (F := E) (pullbackForm g' F p) (fun v hv => ?_)
    exact (pullbackForm_posDef_iff_immersion g' F).mpr himm p v hv
  contMDiff := pullbackForm_contMDiff g' hF

end Pullback

end PoincareConjecture.RiemannianMetric.Induced
