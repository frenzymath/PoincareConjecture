import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Tactic.Linarith








noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1

variable {M : Type*} [TopologicalSpace M] [T2Space M]



theorem isClopen_minimum_disk_annulus_region
    {h : M → Real} (hh : Continuous h)
    (e : OpenPartialHomeomorph E2 M) {r c a b δ : Real}
    (hr : 0 < r) (hrs : closedBall (0 : E2) r ⊆ e.source)
    (hform : ∀ x ∈ e.source, h (e x) = c + ‖x‖ ^ 2)
    (ha : a = c + r ^ 2) (hab : a < b) (hδ : 0 < δ)
    (F : OpenPartialHomeomorph (S1 × Real) M)
    (hsource : F.source = univ ×ˢ Ioo (a - δ) (b + δ))
    (hheight : ∀ q t, t ∈ Ioo (a - δ) (b + δ) → h (F (q, t)) = t)
    (hbottom : range (fun q : S1 => F (q, a)) = e '' sphere (0 : E2) r) :
    IsClopen ((Subtype.val : (h ⁻¹' Iic b) → M) ⁻¹'
      (e '' closedBall (0 : E2) r ∪ F '' (univ ×ˢ Icc a b))) := by
  let K := e '' closedBall (0 : E2) r ∪ F '' (univ ×ˢ Icc a b)
  let B := h ⁻¹' Iic b
  have hstrip : univ ×ˢ Icc a b ⊆ F.source := by
    rw [hsource]
    rintro ⟨q, t⟩ ⟨hq, ht⟩
    exact ⟨hq, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  have hcompact : IsCompact K :=
    ((isCompact_closedBall 0 r).image_of_continuousOn (e.continuousOn.mono hrs)).union
      ((isCompact_univ.prod isCompact_Icc).image_of_continuousOn
        (F.continuousOn.mono hstrip))
  have hband (y : M) (hy : y ∈ F.target) (hyt : h y ∈ Icc a b) :
      y ∈ F '' (univ ×ˢ Icc a b) := by
    have hx := F.map_target hy
    rw [hsource] at hx
    have heq : h y = (F.symm y).2 := by
      simpa only [F.right_inv hy] using hheight (F.symm y).1 (F.symm y).2 hx.2
    exact ⟨F.symm y, ⟨mem_univ _, heq ▸ hyt⟩, F.right_inv hy⟩
  have hdisk (y : M) (hy : y ∈ e.target) (hyt : h y ≤ a) :
      y ∈ e '' closedBall (0 : E2) r := by
    have heq := hform (e.symm y) (e.map_target hy)
    rw [e.right_inv hy] at heq
    refine ⟨e.symm y, mem_closedBall_zero_iff.mpr ?_, e.right_inv hy⟩
    apply (sq_le_sq₀ (norm_nonneg _) hr.le).mp
    rw [ha] at hyt
    linarith
  have hbottomF : e '' sphere (0 : E2) r ⊆ F.target := by
    rw [← hbottom]
    rintro y ⟨q, rfl⟩
    exact F.map_source (hstrip ⟨mem_univ _, le_rfl, hab.le⟩)
  have hbottomE : range (fun q : S1 => F (q, a)) ⊆ e.target := by
    rw [hbottom]
    rintro y ⟨x, hx, rfl⟩
    exact e.map_source (hrs (sphere_subset_closedBall hx))
  let U := e '' ball (0 : E2) r ∪ (e.target ∩ F.target) ∪
    (F.target ∩ h ⁻¹' Ioi a)
  have hU : IsOpen U :=
    ((e.isOpen_image_of_subset_source isOpen_ball (ball_subset_closedBall.trans hrs)).union
      (e.open_target.inter F.open_target)).union
      (F.open_target.inter (isOpen_Ioi.preimage hh))
  have hKU : K ⊆ U := by
    rintro y (⟨x, hx, rfl⟩ | ⟨⟨q, t⟩, hqt, rfl⟩)
    · by_cases hxr : ‖x‖ < r
      · exact Or.inl (Or.inl ⟨x, mem_ball_zero_iff.mpr hxr, rfl⟩)
      · have hxs : x ∈ sphere (0 : E2) r := mem_sphere_zero_iff_norm.mpr
          (le_antisymm (mem_closedBall_zero_iff.mp hx) (le_of_not_gt hxr))
        exact Or.inl (Or.inr ⟨e.map_source (hrs hx), hbottomF ⟨x, hxs, rfl⟩⟩)
    · by_cases hat : a = t
      · subst t
        exact Or.inl (Or.inr ⟨hbottomE ⟨q, rfl⟩, F.map_source (hstrip hqt)⟩)
      · refine Or.inr ⟨F.map_source (hstrip hqt), ?_⟩
        change a < h (F (q, t))
        rw [hheight q t (by rw [hsource] at hstrip; exact (hstrip hqt).2)]
        exact lt_of_le_of_ne hqt.2.1 hat
  have hUB : U ∩ B ⊆ K := by
    rintro y ⟨(hy | hy) | hy, hyb⟩
    · exact Or.inl (image_mono ball_subset_closedBall hy)
    · by_cases hya : h y ≤ a
      · exact Or.inl (hdisk y hy.1 hya)
      · exact Or.inr (hband y hy.2 ⟨(lt_of_not_ge hya).le, hyb⟩)
    · exact Or.inr (hband y hy.1 ⟨hy.2.le, hyb⟩)
  have heq : (Subtype.val : B → M) ⁻¹' K = Subtype.val ⁻¹' U := by
    ext y
    exact ⟨fun hy => hKU hy, fun hy => hUB ⟨hy, y.property⟩⟩
  change IsClopen ((Subtype.val : B → M) ⁻¹' K)
  refine ⟨hcompact.isClosed.preimage continuous_subtype_val, ?_⟩
  rw [heq]
  exact hU.preimage continuous_subtype_val



theorem subset_minimum_disk_annulus_region_of_isPreconnected
    {h : M → Real} (hh : Continuous h)
    (e : OpenPartialHomeomorph E2 M) {r c a b δ : Real}
    (hr : 0 < r) (hrs : closedBall (0 : E2) r ⊆ e.source)
    (hform : ∀ x ∈ e.source, h (e x) = c + ‖x‖ ^ 2)
    (ha : a = c + r ^ 2) (hab : a < b) (hδ : 0 < δ)
    (F : OpenPartialHomeomorph (S1 × Real) M)
    (hsource : F.source = univ ×ˢ Ioo (a - δ) (b + δ))
    (hheight : ∀ q t, t ∈ Ioo (a - δ) (b + δ) → h (F (q, t)) = t)
    (hbottom : range (fun q : S1 => F (q, a)) = e '' sphere (0 : E2) r)
    {C : Set M} (hC : IsPreconnected C) (hCb : C ⊆ h ⁻¹' Iic b)
    (hpC : e 0 ∈ C) :
    C ⊆ e '' closedBall (0 : E2) r ∪ F '' (univ ×ˢ Icc a b) := by
  have hclopen := isClopen_minimum_disk_annulus_region hh e hr hrs hform ha hab hδ
    F hsource hheight hbottom
  have hsub := hC.subset_connectedComponentIn hpC hCb
  intro y hy
  have hycomp := hsub hy
  rw [connectedComponentIn_eq_image (hCb hpC)] at hycomp
  obtain ⟨q, hq, rfl⟩ := hycomp
  exact hclopen.connectedComponent_subset
    (Or.inl ⟨0, mem_closedBall_self hr.le, rfl⟩) hq

end Poincare.Manifold.Schoenflies
