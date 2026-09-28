import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularLevelField
import PoincareConjecture.Proofs.M25.Topology3D.Space3.LevelSliceChart
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false

open Set
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

noncomputable def collarLevelHomeomorph
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ) (u : E3) (t : ℝ) :
    {q : UnitTwoSphere // ⟪u, ψ (q, 0)⟫_ℝ = t} ≃ₜ collarHeightLevel ψ u t := by
  let f : {q : UnitTwoSphere // ⟪u, ψ (q, 0)⟫_ℝ = t} → collarHeightLevel ψ u t :=
    fun q => ⟨ψ (q.1, 0), q.1, q.2, rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · intro p q hpq
      apply Subtype.ext
      have h := hψ.2.1 (x₁ := (p.1, 0)) (x₂ := (q.1, 0))
        ⟨mem_univ _, by norm_num⟩ ⟨mem_univ _, by norm_num⟩ (congrArg Subtype.val hpq)
      exact congrArg Prod.fst h
    · intro y
      obtain ⟨q, hq, hy⟩ := y.2
      exact ⟨⟨q, hq⟩, Subtype.ext hy⟩
  have he := (collar_central_contMDiff ψ hψ).continuous
  let : CompactSpace {q : UnitTwoSphere // ⟪u, ψ (q, 0)⟫_ℝ = t} :=
    isCompact_iff_compactSpace.mp
      (isClosed_eq (continuous_const.inner he) continuous_const).isCompact
  have hc : Continuous f := (he.comp continuous_subtype_val).subtype_mk _
  exact hc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hf)

@[simp] theorem collarLevelHomeomorph_apply
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ) (u : E3) (t : ℝ)
    (q : {q : UnitTwoSphere // ⟪u, ψ (q, 0)⟫_ℝ = t}) :
    (collarLevelHomeomorph ψ hψ u t q : E3) = ψ (q.1, 0) := rfl

theorem collarLevelHomeomorph_symm_eq
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ) (u : E3) (t : ℝ)
    (e : OpenPartialHomeomorph (UnitTwoSphere × ℝ) E3)
    (he : (e : UnitTwoSphere × ℝ → E3) = ψ)
    (hsource : e.source = univ ×ˢ Ioo (-1) 1) (y : collarHeightLevel ψ u t) :
    ((collarLevelHomeomorph ψ hψ u t).symm y).1 = (e.symm (y : E3)).1 := by
  let q := (collarLevelHomeomorph ψ hψ u t).symm y
  have hq : ψ (q.1, 0) = (y : E3) :=
    congrArg Subtype.val ((collarLevelHomeomorph ψ hψ u t).apply_symm_apply y)
  have hqs : (q.1, (0 : ℝ)) ∈ e.source := by
    rw [hsource]
    exact ⟨mem_univ _, by norm_num⟩
  change q.1 = (e.symm (y : E3)).1
  calc
    q.1 = (e.symm (e (q.1, 0))).1 := (congrArg Prod.fst (e.left_inv hqs)).symm
    _ = (e.symm (y : E3)).1 :=
      congrArg (fun z => (e.symm z).1) ((congrFun he (q.1, 0)).trans hq)

theorem collarHeightLevel_locallyConnected
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ) (u : E3) (t : ℝ)
    (hreg : ∀ q : UnitTwoSphere, ⟪u, ψ (q, 0)⟫_ℝ = t →
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun p : UnitTwoSphere => ⟪u, ψ (p, 0)⟫_ℝ) q ≠ 0) :
    LocallyConnectedSpace (collarHeightLevel ψ u t) := by
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun q : UnitTwoSphere => ⟪u, ψ (q, 0)⟫_ℝ) :=
    (InnerProductSpace.toDual ℝ E3 u).contDiff.contMDiff.comp
      (collar_central_contMDiff ψ hψ)
  let : LocallyConnectedSpace {q : UnitTwoSphere // ⟪u, ψ (q, 0)⟫_ℝ = t} :=
    locallyConnected_regular_surface_level (E := E2) (by simp [E2]) _ hf t hreg
  exact (collarLevelHomeomorph ψ hψ u t).symm.isOpenEmbedding.locallyConnectedSpace

theorem finite_collarHeightLevel_components
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ) (u : E3) (t : ℝ)
    (hreg : ∀ q : UnitTwoSphere, ⟪u, ψ (q, 0)⟫_ℝ = t →
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun p : UnitTwoSphere => ⟪u, ψ (p, 0)⟫_ℝ) q ≠ 0) :
    Finite (ConnectedComponents (collarHeightLevel ψ u t)) := by
  let : CompactSpace (collarHeightLevel ψ u t) :=
    isCompact_iff_compactSpace.mp (collarHeightLevel_compact ψ hψ u t)
  let : LocallyConnectedSpace (collarHeightLevel ψ u t) :=
    collarHeightLevel_locallyConnected ψ hψ u t hreg
  infer_instance

end PoincareConjecture.M25.Topology3D
