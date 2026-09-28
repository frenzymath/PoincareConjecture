import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Diffeomorph.EssentialSphere.Extension
import Mathlib.Topology.Connected.Basic

open _root_.AddCircle
open _root_.Poincare
open _root_.PoincareConjecture

namespace M38Schoenflies

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Poincare

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "Cyl" => S2 × ℝ
local notation "I" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

theorem exists_essential_sphere_collar_extension_in_open
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (U : Opens M) (T : Diffeomorph I (𝓡 3) Cyl U ∞)
    {δ : ℝ} (hδ : 0 < δ) (c : OpenPartialHomeomorph Cyl M)
    (hsource : c.source = univ ×ˢ Ioo (-δ) δ) (htarget : c.target ⊆ U)
    (hc : ContMDiffOn I (𝓡 3) ∞ c c.source)
    (hci : ContMDiffOn (𝓡 3) I ∞ c.symm c.target)
    (A B : Set M) (hA : IsOpen A) (hB : IsOpen B)
    (hcA : IsConnected A) (hcB : IsConnected B) (hdis : Disjoint A B)
    (hcover : A ∪ B = (U : Set M) \ range (fun q : S2 => c (q, 0)))
    (hescape : ∀ L : Set M, IsCompact L → L ⊆ U → ¬ A ⊆ L ∧ ¬ B ⊆ L) :
    ∃ η : ℝ, 0 < η ∧ η < δ ∧ ∃ F : Diffeomorph I (𝓡 3) Cyl U ∞,
      ∀ p : Cyl, |p.2| < η → (F p : M) = c p := by
  classical
  have hAU : A ⊆ U := subset_union_left.trans (hcover.le.trans sdiff_subset)
  have hBU : B ⊆ U := subset_union_right.trans (hcover.le.trans sdiff_subset)
  have hUn : Nonempty U := by
    obtain ⟨x, hx⟩ := hcA.nonempty
    exact ⟨⟨x, hAU hx⟩⟩
  let e : OpenPartialHomeomorph Cyl U := (c.symm.subtypeRestr hUn).symm
  have hes : e.source = c.source := by
    change c.source ∩ c ⁻¹' (U.openPartialHomeomorphSubtypeCoe hUn).target = c.source
    rw [Opens.openPartialHomeomorphSubtypeCoe_target]
    exact inter_eq_left.mpr fun x hx => htarget (c.map_source hx)
  have hev (p : Cyl) (hp : p ∈ c.source) : (e p : M) = c p := by
    exact (U.openPartialHomeomorphSubtypeCoe hUn).right_inv
      (by simpa using htarget (c.map_source hp))
  have hec : ContMDiffOn I (𝓡 3) ∞ e e.source := by
    intro p hp
    apply (ContMDiffWithinAt.subtypeVal_comp_iff U e e.source p).mp
    apply ((hc p (hes ▸ hp)).mono (hes ▸ Subset.rfl)).congr
    · intro z hz
      exact hev z (hes ▸ hz)
    · exact hev p (hes ▸ hp)
  have hei : ContMDiffOn (𝓡 3) I ∞ e.symm e.target := by
    have hi : ContMDiffOn (𝓡 3) I ∞ (fun x : U => c.symm (x : M))
        ((Subtype.val : U → M) ⁻¹' c.target) :=
      hci.comp contMDiff_subtype_val.contMDiffOn (fun _ hx => hx)
    have het : e.target = (Subtype.val : U → M) ⁻¹' c.target :=
      c.symm.subtypeRestr_source hUn
    rw [het]
    apply hi.congr
    intro x _
    change (c.symm.subtypeRestr hUn) x = c.symm (x : M)
    rw [OpenPartialHomeomorph.subtypeRestr_coe]
    rfl
  have hz (q : S2) : (q, (0 : ℝ)) ∈ c.source := by
    rw [hsource]
    exact ⟨mem_univ _, neg_lt_zero.mpr hδ, hδ⟩
  have hS : (Subtype.val : U → M) ⁻¹' range (fun q : S2 => c (q, 0)) =
      range (fun q : S2 => e (q, 0)) := by
    ext x
    constructor
    · rintro ⟨q, hq⟩
      exact ⟨q, Subtype.ext ((hev _ (hz q)).trans hq)⟩
    · rintro ⟨q, rfl⟩
      exact ⟨q, (hev _ (hz q)).symm⟩
  have hcov : (Subtype.val : U → M) ⁻¹' A ∪ (Subtype.val : U → M) ⁻¹' B =
      (range (fun q : S2 => e (q, 0)))ᶜ := by
    rw [← preimage_union, hcover, ← hS]
    ext x
    exact and_iff_right x.property
  have hesc (L : Set U) (hL : IsCompact L) :
      ¬ (Subtype.val : U → M) ⁻¹' A ⊆ L ∧ ¬ (Subtype.val : U → M) ⁻¹' B ⊆ L := by
    obtain ⟨hAL, hBL⟩ := hescape ((Subtype.val : U → M) '' L)
      (hL.image continuous_subtype_val) (by rintro x ⟨y, _, rfl⟩; exact y.property)
    constructor
    · intro h
      exact hAL (fun x hx => ⟨⟨x, hAU hx⟩, h hx, rfl⟩)
    · intro h
      exact hBL (fun x hx => ⟨⟨x, hBU hx⟩, h hx, rfl⟩)
  obtain ⟨η, hη, hηδ, F, hF⟩ := exists_essential_sphere_collar_extension T hδ e
    (hes.trans hsource) hec hei ((Subtype.val : U → M) ⁻¹' A)
    ((Subtype.val : U → M) ⁻¹' B) (hA.preimage continuous_subtype_val)
    (hB.preimage continuous_subtype_val)
    (hcA.preimage_of_isOpenMap Subtype.val_injective U.isOpen.isOpenMap_subtype_val
      (by intro x hx; exact ⟨⟨x, hAU hx⟩, rfl⟩))
    (hcB.preimage_of_isOpenMap Subtype.val_injective U.isOpen.isOpenMap_subtype_val
      (by intro x hx; exact ⟨⟨x, hBU hx⟩, rfl⟩))
    (hdis.preimage _) hcov hesc
  refine ⟨η, hη, hηδ, F, fun p hp => ?_⟩
  rw [hF p hp]
  apply hev
  rw [hsource]
  exact ⟨mem_univ _, abs_lt.mp (hp.trans hηδ)⟩

end Poincare

end M38Schoenflies
