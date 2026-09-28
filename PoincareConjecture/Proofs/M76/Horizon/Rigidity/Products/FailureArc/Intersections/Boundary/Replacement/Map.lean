import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Replacement.DiskIdentification
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Bigons.Incidence

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

theorem exists_original_returning_disk_replacement
    {X ι E F : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (J O : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hO : O.faces.Finite)
    {D₀ U₀ W₀ : Set E} {D₁ U₁ W₁ : Set F}
    {a b : E} {c d : F} {f : E → X} {g : F → X}
    (hD₀ : IsFinitePLBallPair P2 D₀ (U₀ ∪ W₀))
    (hD₁ : IsFinitePLBallPair P2 D₁ (U₁ ∪ W₁))
    (hU₀ : IsFinitePLBallPair ℝ U₀ {a, b})
    (hW₀ : IsFinitePLBallPair ℝ W₀ {a, b})
    (hU₁ : IsFinitePLBallPair ℝ U₁ {c, d})
    (hW₁ : IsFinitePLBallPair ℝ W₁ {c, d})
    (hinter₀ : U₀ ∩ W₀ = {a, b}) (hinter₁ : U₁ ∩ W₁ = {c, d})
    (hab : a ≠ b) (hcd : c ≠ d)
    (hcover : D₀ ∪ O.space = J.space) (hseam : D₀ ∩ O.space = W₀)
    (hf : PolyhedralPLInCharts e f J.space) (hg : PolyhedralPLInCharts e g D₁)
    (hfi : InjOn f J.space) (hgi : InjOn g D₁)
    (himage : f '' W₀ = g '' W₁) (ha : f a = g c) (hb : f b = g d)
    (htrace : D₁ ∩ g ⁻¹' (f '' J.space) = W₁) :
    ∃ k : E → X, PolyhedralPLInCharts e k J.space ∧ InjOn k J.space ∧
      Topology.IsEmbedding (fun x : J.space ↦ k x) ∧
      EqOn k f O.space ∧ k '' D₀ = g '' D₁ ∧ k '' U₀ = g '' U₁ ∧
      k '' J.space = (f '' O.space) ∪ (g '' D₁) := by
  have hDJ : D₀ ⊆ J.space := subset_union_left.trans hcover.subset
  have hOJ : O.space ⊆ J.space := subset_union_right.trans hcover.subset
  have hWD : W₀ ⊆ D₀ := subset_union_right.trans hD₀.1
  have hWO : W₀ ⊆ O.space := hseam.symm.subset.trans inter_subset_right
  have hW₁D : W₁ ⊆ D₁ := subset_union_right.trans hD₁.1
  have hcontact : (g '' D₁) ∩ (f '' O.space) = f '' W₀ := by
    rw [inter_comm]
    exact (paired_returning_disks_intersection f g hOJ hWO hW₁D hfi htrace himage).1
  have hcopy := hD₀
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨D, hD, hDs, _⟩, _⟩, _⟩ := hcopy
  have hfD : PolyhedralPLInCharts e f D₀ :=
    hDs ▸ hf.restrict_finite D hD (hDs.subset.trans hDJ)
  obtain ⟨H, hH, hHseam, _, hHU, _⟩ := exists_original_returning_disk_identification he
    hD₀ hD₁ hU₀ hW₀ hU₁ hW₁ hinter₀ hinter₁ hab hcd hfD hg
      (hfi.mono hDJ) hgi himage ha hb
  obtain ⟨v, hv, hvval⟩ := hH
  have hvmap : MapsTo v D₀ D₁ := by
    intro x hx
    rw [← hvval ⟨x, hx⟩]
    exact (H ⟨x, hx⟩).property
  have hvi : InjOn v D₀ := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H.injective (Subtype.ext
      ((hvval ⟨x, hx⟩).trans (hxy.trans (hvval ⟨y, hy⟩).symm))))
  have hvimage : v '' D₀ = D₁ := by
    apply Subset.antisymm (image_subset_iff.mpr hvmap)
    intro y hy
    obtain ⟨x, hx⟩ := H.surjective ⟨y, hy⟩
    exact ⟨x, x.property, (hvval x).symm.trans (congrArg Subtype.val hx)⟩
  have hvU : v '' U₀ = U₁ := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hm := (hHU ⟨x, hD₀.1 (Or.inl hx)⟩).mp hx
      exact hvval ⟨x, hD₀.1 (Or.inl hx)⟩ ▸ hm
    · intro y hy
      obtain ⟨x, hx⟩ := H.surjective ⟨y, hD₁.1 (Or.inl hy)⟩
      have hxy : (H x : F) = y := congrArg Subtype.val hx
      exact ⟨x, (hHU x).mpr (hxy.symm ▸ hy), (hvval x).symm.trans hxy⟩
  have hboundary : EqOn (g ∘ v) f W₀ := by
    intro x hx
    exact (congrArg g (hvval ⟨x, hWD hx⟩)).symm.trans (hHseam ⟨x, hx⟩).symm
  have hgv : PolyhedralPLInCharts e (g ∘ v) D.space :=
    hg.comp_finitePiecewiseAffineOn D hD (hDs.symm ▸ hv)
      (fun _ hx ↦ hvmap (hDs.subset hx))
  obtain ⟨k, hk, hkd, hko⟩ := _root_.Dehn.exists_circle_attachment_map_union he D O hD hO
    hgv (hf.restrict_finite O hO hOJ)
    (fun _ hx hy ↦ hboundary (hseam.subset ⟨hDs.subset hx, hy⟩))
  have hkd' : EqOn k (g ∘ v) D₀ := hDs ▸ hkd
  have hmix (x y : E) (hx : x ∈ D₀) (hy : y ∈ O.space)
      (hxy : g (v x) = f y) : x = y := by
    obtain ⟨z, hz, hzy⟩ := hcontact.subset
      ⟨⟨v x, hvmap hx, hxy⟩, ⟨y, hy, rfl⟩⟩
    have hzy' : z = y := hfi (hDJ (hWD hz)) (hOJ hy) hzy
    have hyW : y ∈ W₀ := hzy' ▸ hz
    exact hvi hx (hWD hyW) (hgi (hvmap hx) (hvmap (hWD hyW))
      (hxy.trans (hboundary hyW).symm))
  have hki : InjOn k J.space := by
    intro x hx y hy hxy
    rcases hcover.symm.subset hx with hx | hx <;>
      rcases hcover.symm.subset hy with hy | hy
    · exact hvi hx hy (hgi (hvmap hx) (hvmap hy)
        ((hkd' hx).symm.trans (hxy.trans (hkd' hy))))
    · exact hmix x y hx hy ((hkd' hx).symm.trans (hxy.trans (hko hy)))
    · exact (hmix y x hy hx ((hkd' hy).symm.trans (hxy.symm.trans (hko hx)))).symm
    · exact hfi (hOJ hx) (hOJ hy) ((hko hx).symm.trans (hxy.trans (hko hy)))
  have hkimage : k '' D₀ = g '' D₁ := by rw [image_congr hkd', image_comp, hvimage]
  have hkU : k '' U₀ = g '' U₁ := by
    rw [image_congr (hkd'.mono (subset_union_left.trans hD₀.1)), image_comp, hvU]
  have hkJ : PolyhedralPLInCharts e k J.space := by simpa only [hDs, hcover] using hk
  let : CompactSpace J.space := isCompact_iff_compactSpace.mp (J.isCompact_space_of_finite hJ)
  have hke : Topology.IsEmbedding (fun x : J.space ↦ k x) :=
    (hkJ.continuousOn.domRestrict.isClosedEmbedding
      (fun x y hxy ↦ Subtype.ext (hki x.property y.property hxy))).isEmbedding
  refine ⟨k, hkJ, hki, hke, hko, hkimage, hkU, ?_⟩
  conv_lhs => rw [← hcover, image_union, hkimage, image_congr hko]
  exact union_comm _ _

end PoincareConjecture.M76.Dehn.Annuli
