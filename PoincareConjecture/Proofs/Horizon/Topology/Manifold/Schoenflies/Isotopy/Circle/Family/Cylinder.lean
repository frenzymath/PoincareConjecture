import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Circle.Family
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Suspension
import PoincareConjecture.Proofs.Horizon.Geometry.Euclidean.HeightCoordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Immersion.FiniteDimensional
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Collar.Differential








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev P2 := Real × E2
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩



theorem exists_supported_cylinder_family_parametrization_within
    {ι : Type*} [Finite ι] {r R : Real} (hr : 0 < r) (hrR : r < R)
    (f : ι → Real × S1 → E2)
    (hf : ∀ i, ContMDiff (𝓘(Real, Real).prod (𝓡 1)) (𝓡 2) ∞ (f i))
    (hemb : ∀ i t, t ∈ Icc (-r) r →
      _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (fun p : S1 => f i (t, p)))
    (hdisjoint : ∀ t ∈ Icc (-r) r, Function.Injective
      (fun z : ι × S1 => f z.1 (t, z.2))) :
    ∃ F : Diffeomorph 𝓘(Real, P2) 𝓘(Real, P2) P2 P2 ∞,
      (∀ z, (F z).1 = z.1) ∧
      (∃ K : Set E2, IsCompact K ∧ ∀ z ∉ closedBall (0 : Real) R ×ˢ K, F z = z) ∧
      (∀ x : E2, F (0, x) = (0, x)) ∧
      ∀ i t, t ∈ Icc (-r) r → ∀ p : S1,
        F (t, f i (0, p)) = (t, f i (t, p)) := by
  obtain ⟨Phi, _, hs, ⟨K, hK, hfix⟩, hmotion⟩ :=
    exists_ambient_isotopy_of_circle_family (by linarith : -r ≤ r) f hf hemb hdisjoint
  let Psi (t : Real) := (Phi 0).symm.trans (Phi t)
  have hPsi : ContDiff Real ∞ (fun z : P2 => Psi z.1 z.2) :=
    hs.comp (contDiff_fst.prodMk ((Phi 0).symm.contMDiff.contDiff.comp contDiff_snd))
  have hPsi0 (x : E2) : Psi 0 x = x := (Phi 0).apply_symm_apply x
  have hPsifix (t : Real) (x : E2) (hx : x ∉ K) : Psi t x = x := by
    have hsymm : (Phi 0).symm x = x := by
      apply (Phi 0).injective
      change Phi 0 ((Phi 0).symm x) = Phi 0 x
      rw [(Phi 0).apply_symm_apply, hfix 0 x hx]
    change Phi t ((Phi 0).symm x) = x
    rw [hsymm, hfix t x hx]
  obtain ⟨F, hheight, hF, _, hFfix⟩ :=
    exists_supported_family_suspension Psi hPsi hPsi0 hK hPsifix hr hrR
  refine ⟨F, hheight, ⟨K, hK, hFfix⟩, ?_, ?_⟩
  · intro x
    rw [hF 0 (by simpa using hr.le), hPsi0]
  · intro i t ht p
    have htb : t ∈ closedBall (0 : Real) r := by
      simpa only [mem_closedBall, Real.dist_eq, sub_zero] using abs_le.mpr ht
    rw [hF t htb]
    congr 1
    change Phi t ((Phi 0).symm (f i (0, p))) = f i (t, p)
    rw [← hmotion i 0 (by constructor <;> linarith) p, (Phi 0).symm_apply_apply]
    exact hmotion i t ht p


theorem exists_supported_cylinder_family_parametrization
    {ι : Type*} [Finite ι] {r : Real} (hr : 0 < r) (f : ι → Real × S1 → E2)
    (hf : ∀ i, ContMDiff (𝓘(Real, Real).prod (𝓡 1)) (𝓡 2) ∞ (f i))
    (hemb : ∀ i t, t ∈ Icc (-r) r →
      _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (fun p : S1 => f i (t, p)))
    (hdisjoint : ∀ t ∈ Icc (-r) r, Function.Injective
      (fun z : ι × S1 => f z.1 (t, z.2))) :
    ∃ F : Diffeomorph 𝓘(Real, P2) 𝓘(Real, P2) P2 P2 ∞,
      (∀ z, (F z).1 = z.1) ∧
      (∃ K : Set P2, IsCompact K ∧ ∀ z ∉ K, F z = z) ∧
      ∀ i t, t ∈ Icc (-r) r → ∀ p : S1,
        F (t, f i (0, p)) = (t, f i (t, p)) := by
  obtain ⟨F, hheight, ⟨K, hK, hfix⟩, _, hF⟩ :=
    exists_supported_cylinder_family_parametrization_within hr (lt_add_one r) f hf hemb hdisjoint
  exact ⟨F, hheight, ⟨closedBall (0 : Real) (r + 1) ×ˢ K,
    (isCompact_closedBall _ _).prod hK, hfix⟩, hF⟩



theorem exists_supported_ambient_cylinder_family_within
    {ι : Type*} [Finite ι] {v : E3} (hv : ‖v‖ = 1) (c : Real)
    {r R : Real} (hr : 0 < r) (hrR : r < R) (f : ι → Real × S1 → (Real ∙ v)ᗮ)
    (hf : ∀ i, ContMDiff (𝓘(Real, Real).prod (𝓡 1)) 𝓘(Real, (Real ∙ v)ᗮ) ∞ (f i))
    (hemb : ∀ i t, t ∈ Icc (-r) r → _root_.Manifold.IsSmoothEmbedding
      (𝓡 1) 𝓘(Real, (Real ∙ v)ᗮ) ∞ (fun p : S1 => f i (t, p)))
    (hdisjoint : ∀ t ∈ Icc (-r) r, Function.Injective
      (fun z : ι × S1 => f z.1 (t, z.2))) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ x, inner Real v (F x) = inner Real v x) ∧
      (∃ K : Set E3, IsCompact K ∧ K ⊆ {x | |inner Real v x - c| ≤ R} ∧
        ∀ x ∉ K, F x = x) ∧
      EqOn F id {x | inner Real v x = c} ∧
      ∀ i t, t ∈ Icc (-r) r → ∀ p : S1,
        F ((c + t) • v + (f i (0, p) : E3)) =
          (c + t) • v + (f i (t, p) : E3) := by
  let J : (Real ∙ v)ᗮ ≃ₗᵢ[Real] E2 :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (by
      intro heq
      simp [heq] at hv)).repr
  let g : ι → Real × S1 → E2 := fun i z => J (f i z)
  have hg (i : ι) : ContMDiff (𝓘(Real, Real).prod (𝓡 1)) (𝓡 2) ∞ (g i) :=
    J.toContinuousLinearEquiv.contDiff.contMDiff.comp (hf i)
  have hgemb (i : ι) (t : Real) (ht : t ∈ Icc (-r) r) :
      _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (fun p : S1 => g i (t, p)) := by
    have hs := (hemb i t ht).contMDiff
    apply Poincare.Geometry.Manifold.isSmoothEmbedding_of_injective_mfderiv
      (J.toContinuousLinearEquiv.contDiff.contMDiff.comp hs)
      (J.injective.comp (hemb i t ht).isEmbedding.injective)
    intro p
    have hJ : ContMDiff 𝓘(Real, (Real ∙ v)ᗮ) (𝓡 2) ∞ J.toContinuousLinearEquiv :=
      J.toContinuousLinearEquiv.contDiff.contMDiff
    change Function.Injective (mfderiv (𝓡 1) (𝓡 2)
      (J.toContinuousLinearEquiv ∘ (fun q => f i (t, q))) p)
    rw [mfderiv_comp p (hJ.mdifferentiable (by simp) _) (hs.mdifferentiable (by simp) p)]
    exact (J.toContinuousLinearEquiv.toDiffeomorph.mfderivToContinuousLinearEquiv
      (by simp) (f i (t, p))).injective.comp
      (((hemb i t ht).isImmersion.isImmersionAt p).injective_mfderiv_modelWithCornersSelf
        (by simp))
  have hgdisjoint (t : Real) (ht : t ∈ Icc (-r) r) :
      Function.Injective (fun z : ι × S1 => g z.1 (t, z.2)) :=
    J.injective.comp (hdisjoint t ht)
  obtain ⟨G, hGt, ⟨Kplane, hKplane, hGfix⟩, hGzero, hG⟩ :=
    exists_supported_cylinder_family_parametrization_within hr hrR g hg hgemb hgdisjoint
  let K := closedBall (0 : Real) R ×ˢ Kplane
  have hK : IsCompact K := (isCompact_closedBall _ _).prod hKplane
  let A := ((ContinuousLinearEquiv.refl Real Real).prodCongr
    J.symm.toContinuousLinearEquiv).trans (Poincare.Geometry.Euclidean.heightCoordinates hv)
  let T : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ := {
    toEquiv := Equiv.addRight (c • v)
    contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
    contMDiff_invFun := (contDiff_id.add contDiff_const).contMDiff }
  let D := A.toDiffeomorph.trans T
  have hD (z : Real × E2) : D z = (c + z.1) • v + (J.symm z.2 : E3) := by
    change z.1 • v + (J.symm z.2 : E3) + c • v = _
    rw [add_smul]
    abel
  have hheight (z : Real × E2) : inner Real v (D z) = c + z.1 := by
    rw [hD]
    simp [inner_add_right, inner_smul_right, hv,
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp (J.symm z.2).property]
  let F := (D.symm.trans G).trans D
  refine ⟨F, ?_, ⟨D '' K, hK.image D.contMDiff.continuous, ?_, ?_⟩, ?_, ?_⟩
  · intro x
    change inner Real v (D (G (D.symm x))) = inner Real v x
    rw [hheight, hGt, ← hheight, D.apply_symm_apply]
  · rintro _ ⟨z, hz, rfl⟩
    change |inner Real v (D z) - c| ≤ R
    rw [hheight]
    simpa only [K, mem_prod, mem_closedBall, Real.dist_eq, sub_zero,
      add_sub_cancel_left] using hz.1
  · intro x hx
    have hnot : D.symm x ∉ K := by
      intro hin
      exact hx ⟨D.symm x, hin, D.apply_symm_apply x⟩
    change D (G (D.symm x)) = x
    rw [hGfix _ hnot, D.apply_symm_apply]
  · intro x hx
    have hzero : (D.symm x).1 = 0 := by
      have hh := hheight (D.symm x)
      rw [D.apply_symm_apply, hx] at hh
      linarith
    have hz : D.symm x = (0, (D.symm x).2) := Prod.ext hzero rfl
    change D (G (D.symm x)) = x
    rw [hz, hGzero, ← hz, D.apply_symm_apply]
  · intro i t ht p
    have hDg (s : Real) : D (t, g i (s, p)) = (c + t) • v + (f i (s, p) : E3) := by
      rw [hD]
      simp [g]
    rw [← hDg 0]
    change D (G (D.symm (D (t, g i (0, p))))) = _
    rw [D.symm_apply_apply, hG i t ht p, hDg t]


theorem exists_supported_ambient_cylinder_family
    {ι : Type*} [Finite ι] {v : E3} (hv : ‖v‖ = 1) (c : Real)
    {r : Real} (hr : 0 < r) (f : ι → Real × S1 → (Real ∙ v)ᗮ)
    (hf : ∀ i, ContMDiff (𝓘(Real, Real).prod (𝓡 1)) 𝓘(Real, (Real ∙ v)ᗮ) ∞ (f i))
    (hemb : ∀ i t, t ∈ Icc (-r) r → _root_.Manifold.IsSmoothEmbedding
      (𝓡 1) 𝓘(Real, (Real ∙ v)ᗮ) ∞ (fun p : S1 => f i (t, p)))
    (hdisjoint : ∀ t ∈ Icc (-r) r, Function.Injective
      (fun z : ι × S1 => f z.1 (t, z.2))) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ x, inner Real v (F x) = inner Real v x) ∧
      (∃ K : Set E3, IsCompact K ∧ ∀ x ∉ K, F x = x) ∧
      ∀ i t, t ∈ Icc (-r) r → ∀ p : S1,
        F ((c + t) • v + (f i (0, p) : E3)) =
          (c + t) • v + (f i (t, p) : E3) := by
  obtain ⟨F, hheight, ⟨K, hK, _, hfix⟩, _, hF⟩ :=
    exists_supported_ambient_cylinder_family_within hv c hr (lt_add_one r) f hf hemb hdisjoint
  exact ⟨F, hheight, ⟨K, hK, hfix⟩, hF⟩

end Poincare.Manifold.Schoenflies
