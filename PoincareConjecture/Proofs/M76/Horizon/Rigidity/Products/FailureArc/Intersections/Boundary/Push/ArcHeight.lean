import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Replacement.ArcExtension
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolygonalStripDiskAttachment
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLPrescribedBoundaryArc
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCoordinates

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

open PolygonalCrossingResolution
local notation "P2" => (ℝ × ℝ)

theorem exists_finitePL_disk_arc_height
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {d q W : Set E} {a b : E}
    (hd : IsFinitePLBallPair P2 d q) (hW : IsFinitePLBallPair ℝ W {a, b})
    (hWq : W ⊆ q) (hab : a ≠ b) :
    ∃ v : E → ℝ, FinitePiecewiseAffineOn v d ∧
      ∀ x ∈ d, 0 ≤ v x ∧ v x ≤ 1 ∧ (v x = 0 ↔ x ∈ W) := by
  have hs : IsFinitePLBallPair P2 source stripRim :=
    (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)).prod
      (isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num))
  obtain ⟨hbottom, p, hp, hpval⟩ := exists_arm_parameter (-1)
  have hbottomrim : arm (-1) ⊆ stripRim := fun x hx ↦ Or.inr ⟨hx.1, Or.inl hx.2⟩
  have h01 : ((0, -1) : P2) ≠ (1, -1) := by norm_num
  obtain ⟨U, hU, hbottomU, hinterU⟩ := hs.exists_boundary_arc_complement hbottom hbottomrim h01
  obtain ⟨V, hV, hWV, hinterV⟩ := hd.exists_boundary_arc_complement hW hWq hab
  obtain ⟨w, hw, hw0, hw1⟩ := hW.exists_unitInterval_chart_with_endpoints hab
  let r := w.symm.trans p
  have hr : r.IsFinitePL := hw.symm.trans hp
  have hra : (r ⟨a, hW.1 (by simp)⟩ : P2) = (0, -1) := by
    have ha : (⟨a, hW.1 (by simp)⟩ : W) = w 0 := Subtype.ext hw0.symm
    simp only [ha, r, Homeomorph.trans_apply, w.symm_apply_apply, hpval]
    rfl
  have hrb : (r ⟨b, hW.1 (by simp)⟩ : P2) = (1, -1) := by
    have hb : (⟨b, hW.1 (by simp)⟩ : W) = w 1 := Subtype.ext hw1.symm
    simp only [hb, r, Homeomorph.trans_apply, w.symm_apply_apply, hpval]
    rfl
  have hd' : IsFinitePLBallPair P2 d (V ∪ W) := by rw [union_comm, hWV]; exact hd
  have hs' : IsFinitePLBallPair P2 source (U ∪ arm (-1)) := by rw [union_comm, hbottomU]; exact hs
  obtain ⟨H, hH, _, _, hHW⟩ := exists_disk_homeomorph_prescribed_arc hd' hs' hV hW hU
    (by rw [inter_comm]; exact hinterV) (by rw [inter_comm]; exact hinterU) r hr hra hrb
  obtain ⟨f, hf, hHf⟩ := hH
  let height : P2 →ᴬ[ℝ] ℝ :=
    (1 / 2 : ℝ) • ((ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap +
      ContinuousAffineMap.const ℝ P2 1)
  refine ⟨height ∘ f, hf.postcomp height, ?_⟩
  intro x hx
  have hbnd := (H ⟨x, hx⟩).property.2
  have hwiff := hHW ⟨x, hx⟩
  rw [hHf] at hbnd hwiff
  change -1 ≤ (f x).2 ∧ (f x).2 ≤ 1 at hbnd
  have hfx := (H ⟨x, hx⟩).property.1
  rw [hHf] at hfx
  have hwiff' : x ∈ W ↔ (f x).2 = -1 := by
    simpa only [arm, mem_prod, mem_singleton_iff, hfx, true_and] using hwiff
  change 0 ≤ (1 / 2 : ℝ) * ((f x).2 + 1) ∧
    (1 / 2 : ℝ) * ((f x).2 + 1) ≤ 1 ∧
    ((1 / 2 : ℝ) * ((f x).2 + 1) = 0 ↔ x ∈ W)
  refine ⟨by linarith, by linarith, ?_⟩
  rw [hwiff']
  constructor <;> intro h <;> linarith

end PoincareConjecture.M76.Dehn.Annuli
