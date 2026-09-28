import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.CyclicPanels.Construction
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.CyclicPanels.CappedDisk
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.OriginalSphere







set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli.CyclicPanels

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Rect" => (I ×ˢ I : Set P2)

theorem nonempty_original_sphere_of_annulus_and_disks
    {X ι F₀ F₁ : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup F₀] [NormedSpace ℝ F₀] [FiniteDimensional ℝ F₀]
    [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {L d : ℝ} (hd : 0 < d) (hwidth : 4 * d < L)
    {g : P2 → X} {f₀ : F₀ → X} {f₁ : F₁ → X}
    {c₀ q₀ : Set F₀} {c₁ q₁ : Set F₁}
    (hg : PolyhedralPLInCharts e g (squareAnnulus L d))
    (hgi : InjOn g (squareAnnulus L d))
    (hc₀ : IsFinitePLBallPair P2 c₀ q₀) (hc₁ : IsFinitePLBallPair P2 c₁ q₁)
    (hf₀ : PolyhedralPLInCharts e f₀ c₀) (hf₁ : PolyhedralPLInCharts e f₁ c₁)
    (hi₀ : InjOn f₀ c₀) (hi₁ : InjOn f₁ c₁)
    (hrim₀ : g '' frontier (_root_.Dehn.annulusSquare L (-d)) = f₀ '' q₀)
    (hrim₁ : g '' frontier (_root_.Dehn.annulusSquare L d) = f₁ '' q₁)
    (hcontact₀ : (g '' squareAnnulus L d) ∩ (f₀ '' c₀) = f₀ '' q₀)
    (hcontact₁ : (g '' squareAnnulus L d) ∩ (f₁ '' c₁) = f₁ '' q₁)
    (hdis : Disjoint (f₀ '' c₀) (f₁ '' c₁)) :
    Nonempty (ChartwisePLSphere e
      ((g '' squareAnnulus L d) ∪ ((f₀ '' c₀) ∪ (f₁ '' c₁)))) := by
  obtain ⟨k,hk,hki,_,hkimage,hkrim⟩ := exists_original_capped_annulus_disk he hd hwidth
    hg hgi hc₁ hf₁ hi₁ hrim₁ (hcontact₁.trans hrim₁.symm)
  have houter := _root_.Dehn.isFinitePLBallPair_annulusSquare
    (show 2 * (-d) < L by linarith)
  have hcontact : (k '' _root_.Dehn.annulusSquare L (-d)) ∩ (f₀ '' c₀) =
      k '' frontier (_root_.Dehn.annulusSquare L (-d)) := by
    rw [hkimage,union_inter_distrib_right,hdis.symm.inter_eq,empty_union,hcontact₀,hkrim,hrim₀]
  have h := nonempty_original_sphere_of_disk_union he houter hc₀ hk hf₀ hki hi₀
    (hkrim.trans hrim₀) hcontact
  rw [hkimage] at h
  have hsets : ((f₁ '' c₁) ∪ (g '' squareAnnulus L d)) ∪ (f₀ '' c₀) =
      (g '' squareAnnulus L d) ∪ ((f₀ '' c₀) ∪ (f₁ '' c₁)) := by
    ext x
    simp only [mem_union]
    tauto
  exact hsets ▸ h

theorem nonempty_original_sphere_of_eight_panels
    {X ι F₀ F₁ : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup F₀] [NormedSpace ℝ F₀] [FiniteDimensional ℝ F₀]
    [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    {e : ι → OpenPartialHomeomorph X V3}
    (hcover : ∀ x : X, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (f : Fin 8 → P2 → X) (hf : ∀ i, PolyhedralPLInCharts e (f i) Rect)
    (hfi : ∀ i, InjOn (f i) Rect)
    (hseam : ∀ i j : Fin 8, i.val + 1 = j.val → ∀ t ∈ I, f i (1,t) = f j (0,t))
    (hclose : ∀ t ∈ I, f 7 (1,t) = f 0 (0,t))
    (hcontact : ∀ i j : Fin 8, i.val + 1 = j.val →
      (f i '' Rect) ∩ (f j '' Rect) = f i '' ({1} ×ˢ I))
    (hend : (f 0 '' Rect) ∩ (f 7 '' Rect) = f 0 '' ({0} ×ˢ I))
    (hfar : ∀ i j : Fin 8, i.val + 1 < j.val →
      ¬ (i = 0 ∧ j = 7) → Disjoint (f i '' Rect) (f j '' Rect))
    {f₀ : F₀ → X} {f₁ : F₁ → X} {c₀ q₀ : Set F₀} {c₁ q₁ : Set F₁}
    (hc₀ : IsFinitePLBallPair P2 c₀ q₀) (hc₁ : IsFinitePLBallPair P2 c₁ q₁)
    (hf₀ : PolyhedralPLInCharts e f₀ c₀) (hf₁ : PolyhedralPLInCharts e f₁ c₁)
    (hi₀ : InjOn f₀ c₀) (hi₁ : InjOn f₁ c₁)
    (hrim₀ : (⋃ i, f i '' (I ×ˢ {0})) = f₀ '' q₀)
    (hrim₁ : (⋃ i, f i '' (I ×ˢ {1})) = f₁ '' q₁)
    (hcontact₀ : (⋃ i, f i '' Rect) ∩ (f₀ '' c₀) = f₀ '' q₀)
    (hcontact₁ : (⋃ i, f i '' Rect) ∩ (f₁ '' c₁) = f₁ '' q₁)
    (hdis : Disjoint (f₀ '' c₀) (f₁ '' c₁)) :
    Nonempty (ChartwisePLSphere e ((⋃ i, f i '' Rect) ∪ ((f₀ '' c₀) ∪ (f₁ '' c₁)))) := by
  obtain ⟨g,hg,hgi,hgimage,_,hgr₀,hgr₁⟩ := exists_original_eight_panel_annulus
    hcover hcompat f hf hfi hseam hclose hcontact hend hfar
  have hginj : InjOn g (squareAnnulus (2 : ℝ) (1 / 8)) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hgi.injective (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩) hxy)
  have h := nonempty_original_sphere_of_annulus_and_disks hcompat
    (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num : 4 * (1 / 8 : ℝ) < 2)
    hg hginj hc₀ hc₁ hf₀ hf₁ hi₀ hi₁ (hgr₀.trans hrim₀) (hgr₁.trans hrim₁)
    (by rw [hgimage]; exact hcontact₀) (by rw [hgimage]; exact hcontact₁) hdis
  simpa only [hgimage] using h

end PoincareConjecture.M76.Dehn.Annuli.CyclicPanels
