import PoincareConjecture.Proofs.M32.Claim11_34.Isotopy.Parameter
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas















noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology Bundle

universe u

namespace PoincareConjecture.M32

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]





theorem exists_smooth_local_sphere_velocity
    {F : ℝ × UnitTwoSphere → M}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3) ∞ F)
    (hembed : ∀ t, Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun q => F (t, q)))
    {U : Set M} (hU : IsOpen U) (hFU : ∀ t, range (fun q => F (t, q)) ⊆ U)
    (s : ℝ) (q₀ : UnitTwoSphere) :
    ∃ (W : Set (ℝ × M)) (X : ℝ → (x : M) → TangentSpace (𝓡 3) x),
      IsOpen W ∧ (s, F (s, q₀)) ∈ W ∧ W ⊆ univ ×ˢ U ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3).tangent ∞
        (fun z : ℝ × M => (⟨z.2, X z.1 z.2⟩ : TangentBundle (𝓡 3) M)) W ∧
      ∀ t q, (t, F (t, q)) ∈ W →
        HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 3) (fun τ => F (τ, q)) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (F (t, q)))) := by
  obtain ⟨W₀, r, hW₀, hsW₀, hW₀U, hr, hrecover⟩ :=
    exists_smooth_local_sphere_parameter hF hembed hU hFU s q₀
  let IZ := 𝓘(ℝ, ℝ).prod (𝓡 2)
  let IP := 𝓘(ℝ, ℝ).prod (𝓡 3)
  let E := EuclideanSpace ℝ (Fin 3)
  let p := F (s, q₀)
  let c := extChartAt (𝓡 3) p
  have hcs : IsOpen c.source := isOpen_extChartAt_source p
  have hct : IsOpen c.target := isOpen_extChartAt_target p
  have hc : ContMDiffOn (𝓡 3) (𝓡 3) ∞ c c.source := by
    simpa only [c, extChartAt_source] using
      (contMDiffOn_extChartAt (I := 𝓡 3) (x := p) (n := ∞))
  have hci : ContMDiffOn (𝓡 3) (𝓡 3) ∞ c.symm c.target :=
    contMDiffOn_extChartAt_symm p
  let v : (z : ℝ × UnitTwoSphere) → TangentSpace (𝓡 3) (F z) :=
    fun z => mfderiv IZ (𝓡 3) F z (1, 0)
  have htime : ContMDiff IZ 𝓘(ℝ, ℝ).tangent ∞
      (fun z : ℝ × UnitTwoSphere => (⟨z.1, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    intro z
    exact ((contMDiffAt_vectorSpace_iff_contDiffAt).mpr
      (contDiffAt_const (c := (1 : ℝ)))).comp z contMDiffAt_fst
  have hzero : ContMDiff IZ (𝓡 2).tangent ∞
      (fun z : ℝ × UnitTwoSphere => (⟨z.2, 0⟩ : TangentBundle (𝓡 2) UnitTwoSphere)) :=
    (Bundle.contMDiff_zeroSection ℝ (TangentSpace (𝓡 2) : UnitTwoSphere → Type)).comp
      contMDiff_snd
  have htimeVector : ContMDiff IZ IZ.tangent ∞
      (fun z : ℝ × UnitTwoSphere =>
        (⟨z, (1, 0)⟩ : TangentBundle IZ (ℝ × UnitTwoSphere))) :=
    (contMDiff_equivTangentBundleProd_symm
      (I := 𝓘(ℝ, ℝ)) (M := ℝ) (I' := 𝓡 2) (M' := UnitTwoSphere)).comp
      (htime.prodMk hzero)
  have hv : ContMDiff IZ (𝓡 3).tangent ∞
      (fun z => (⟨F z, v z⟩ : TangentBundle (𝓡 3) M)) :=
    (hF.contMDiff_tangentMap (m := ∞) (by simp)).comp htimeVector
  have hdc : ContMDiffOn (𝓡 3).tangent (𝓡 3).tangent ∞
      (tangentMap (𝓡 3) (𝓡 3) c)
      {z : TangentBundle (𝓡 3) M | z.proj ∈ c.source} := by
    apply (hc.contMDiffOn_tangentMapWithin (m := ∞) (by simp) hcs.uniqueMDiffOn).congr
    intro z hz
    simp only [tangentMap, tangentMapWithin, mfderivWithin_of_isOpen hcs hz]
  have hdci : ContMDiffOn (𝓡 3).tangent (𝓡 3).tangent ∞
      (tangentMap (𝓡 3) (𝓡 3) c.symm)
      {z : TangentBundle (𝓡 3) E | z.proj ∈ c.target} := by
    apply (hci.contMDiffOn_tangentMapWithin (m := ∞) (by simp) hct.uniqueMDiffOn).congr
    intro z hz
    simp only [tangentMap, tangentMapWithin, mfderivWithin_of_isOpen hct hz]
  let A := F ⁻¹' c.source
  have hA : IsOpen A := hcs.preimage hF.continuous
  let w : ℝ × UnitTwoSphere → E := fun z => mfderiv (𝓡 3) (𝓡 3) c (F z) (v z)
  have hw : ContMDiffOn IZ (𝓡 3) ∞ w A :=
    (contMDiff_snd_tangentBundle_modelSpace E (𝓡 3)).comp_contMDiffOn
      (hdc.comp hv.contMDiffOn (fun z hz => hz))
  let κ : ℝ × M → ℝ × UnitTwoSphere := fun z => (z.1, r z)
  have hκ : ContMDiffOn IP IZ ∞ κ W₀ := contMDiff_fst.contMDiffOn.prodMk hr
  let W₁ := W₀ ∩ (univ ×ˢ c.source)
  have hW₁ : IsOpen W₁ := hW₀.inter (isOpen_univ.prod hcs)
  let W := W₁ ∩ κ ⁻¹' A
  have hW : IsOpen W := (hκ.mono inter_subset_left).continuousOn.isOpen_inter_preimage hW₁ hA
  have hp : p ∈ c.source := mem_extChartAt_source p
  have hsW : (s, F (s, q₀)) ∈ W := by
    refine ⟨⟨hsW₀, ⟨mem_univ _, hp⟩⟩, ?_⟩
    change F (s, r (s, F (s, q₀))) ∈ c.source
    rw [hrecover s q₀ hsW₀]
    exact hp
  let X : ℝ → (x : M) → TangentSpace (𝓡 3) x :=
    fun t x => mfderiv (𝓡 3) (𝓡 3) c.symm (c x) (w (κ (t, x)))
  have hcx : ContMDiffOn IP (𝓡 3) ∞ (fun z : ℝ × M => c z.2) W :=
    hc.comp contMDiff_snd.contMDiffOn (fun z hz => hz.1.2.2)
  have hwκ : ContMDiffOn IP (𝓡 3) ∞ (w ∘ κ) W :=
    hw.comp (hκ.mono (fun z hz => hz.1.1)) (fun z hz => hz.2)
  have hB : ContMDiffOn IP (𝓡 3).tangent ∞
      (fun z : ℝ × M => (⟨c z.2, w (κ z)⟩ : TangentBundle (𝓡 3) E)) W := by
    have hprod : ContMDiffOn IP ((𝓡 3).prod (𝓡 3)) ∞
        (fun z : ℝ × M => (c z.2, w (κ z))) W := hcx.prodMk hwκ
    rw [chartedSpaceSelf_prod] at hprod
    exact (contMDiff_tangentBundleModelSpaceHomeomorph_symm (I := 𝓡 3)).comp_contMDiffOn hprod
  have hX : ContMDiffOn IP (𝓡 3).tangent ∞
      (fun z : ℝ × M => (⟨z.2, X z.1 z.2⟩ : TangentBundle (𝓡 3) M)) W := by
    apply (hdci.comp hB (fun z hz => c.map_source hz.1.2.2)).congr
    intro z hz
    change (⟨z.2, X z.1 z.2⟩ : TangentBundle (𝓡 3) M) =
      ⟨c.symm (c z.2), mfderiv (𝓡 3) (𝓡 3) c.symm (c z.2) (w (κ z))⟩
    rw [c.left_inv hz.1.2.2]
    rfl
  have hpush (x : M) (hx : x ∈ c.source) (a : TangentSpace (𝓡 3) x) :
      mfderiv (𝓡 3) (𝓡 3) c.symm (c x) (mfderiv (𝓡 3) (𝓡 3) c x a) = a := by
    have hh := congrArg (fun L => L a)
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := 𝓡 3) hx)
    simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ,
      ContinuousLinearMap.comp_apply] at hh
    exact hh
  refine ⟨W, X, hW, hsW, fun z hz => hW₀U hz.1.1, hX, ?_⟩
  intro t q htq
  have heq : X t (F (t, q)) = v (t, q) := by
    change mfderiv (𝓡 3) (𝓡 3) c.symm (c (F (t, q)))
      (w (t, r (t, F (t, q)))) = v (t, q)
    rw [hrecover t q htq.1.1]
    exact hpush (F (t, q)) htq.1.2.2 (v (t, q))
  have hcurve := ((hF.mdifferentiable (by simp) (t, q)).hasMFDerivAt).comp t
    ((hasMFDerivAt_id (I := 𝓘(ℝ, ℝ)) t).prodMk
      (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 2) q t))
  apply hcurve.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  change ℝ at a
  change mfderiv IZ (𝓡 3) F (t, q) (a, 0) = a • X t (F (t, q))
  rw [heq]
  have hpair : (a, (0 : EuclideanSpace ℝ (Fin 2))) =
      a • ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin 2))) := by
    ext <;> simp
  rw [hpair, map_smul]

end PoincareConjecture.M32
