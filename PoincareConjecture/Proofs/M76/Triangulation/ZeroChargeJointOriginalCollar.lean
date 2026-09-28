import PoincareConjecture.Proofs.M76.Triangulation.ZeroChargeJointSurface
import PoincareConjecture.Proofs.M76.Mathlib.OriginalBoxProductCoordinates












set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.ZeroChargeJoint

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {n : ℕ}





theorem exists_joint_cylinder_of_original_polygon_collar
    (P : Polygon V (n + 3)) (hP : P.HasSimplicialEdges)
    (hPinj : Function.Injective P) (hdim : Module.finrank ℝ E = 2)
    {r tau c : ℝ} (hr : 0 < r) (htau : 0 < tau)
    {T S : Set V} (A : V → ℝ)
    (h : (E × ℝ) ≃ᴬ[ℝ] V) (hh : ∀ p, A (h p) = c + p.2)
    (G : (P.boundary ℝ ×ˢ (Icc (-r) r ×ˢ Icc (-r) r) :
      Set (V × (ℝ × ℝ))) ≃ₜ T) (hG : G.IsFinitePL)
    (hGheight : ∀ p, A (G p) = c + (p : V × (ℝ × ℝ)).2.1)
    (hGsurface : ∀ p, (G p : V) ∈ S ↔ (p : V × (ℝ × ℝ)).2.2 = 0)
    (hGcore : ∀ p : (P.boundary ℝ ×ˢ (Icc (-r) r ×ˢ Icc (-r) r) :
      Set (V × (ℝ × ℝ))), (p : V × (ℝ × ℝ)).2 = 0 →
        (G p : V) = (p : V × (ℝ × ℝ)).1)
    (hband : S ∩ {x | |A x - c| ≤ tau} ⊆ T)
    {d : Set E} (hd : IsCompact d) :
    ∃ epsilon : ℝ, epsilon ∈ Ioo 0 (min r tau) ∧
      ∃ K : SimplicialComplex ℝ E, K.faces.Finite ∧ Convex ℝ K.space ∧
        d ⊆ interior K.space ∧
        (∀ v ∈ P.boundary ℝ, (h.symm v).1 ∈ interior K.space) ∧
        ∃ e : (K.space ×ˢ Icc (-epsilon) epsilon : Set (E × ℝ)) ≃ₜ
            (K.space ×ˢ Icc (-epsilon) epsilon),
          e.IsFinitePL ∧
          (∀ p, (e p : E × ℝ).2 = (p : E × ℝ).2) ∧
          (∀ p : (K.space ×ˢ Icc (-epsilon) epsilon : Set (E × ℝ)),
            (p : E × ℝ).2 = 0 → e p = p) ∧
          (∀ p, (e p : E × ℝ) ∈ h ⁻¹' S ↔
            (p : E × ℝ).1 ∈ (fun v : V => (h.symm v).1) '' P.boundary ℝ) ∧
          (h ⁻¹' S) ∩ {p | p.2 ∈ Icc (-epsilon) epsilon} ⊆
            K.space ×ˢ Icc (-epsilon) epsilon := by
  obtain ⟨g, hg, hgval⟩ := hG
  let F : V × (ℝ × ℝ) → E × ℝ := h.symm ∘ g
  have hF : FinitePiecewiseAffineOn F
      (P.boundary ℝ ×ˢ (Icc (-r) r ×ˢ Icc (-r) r)) :=
    hg.postcomp h.symm.toContinuousAffineMap
  have hFinj : InjOn F (P.boundary ℝ ×ˢ (Icc (-r) r ×ˢ Icc (-r) r)) := by
    intro p hp q hq heq
    have hgeq : g p = g q := h.symm.injective heq
    have hGpq : G ⟨p, hp⟩ = G ⟨q, hq⟩ :=
      Subtype.ext ((hgval ⟨p, hp⟩).trans (hgeq.trans (hgval ⟨q, hq⟩).symm))
    exact congrArg Subtype.val (G.injective hGpq)
  have hFheight : ∀ p ∈ P.boundary ℝ ×ˢ (Icc (-r) r ×ˢ Icc (-r) r),
      (F p).2 = p.2.1 := by
    intro p hp
    have ht := hh (h.symm (g p))
    rw [h.apply_symm_apply, ← hgval ⟨p, hp⟩] at ht
    change (h.symm (g p)).2 = p.2.1
    rw [← hgval ⟨p, hp⟩]
    exact add_left_cancel (ht.symm.trans (hGheight ⟨p, hp⟩))
  have hFsurface : ∀ p ∈ P.boundary ℝ ×ˢ (Icc (-r) r ×ˢ Icc (-r) r),
      F p ∈ h ⁻¹' S ↔ p.2.2 = 0 := by
    intro p hp
    change h (h.symm (g p)) ∈ S ↔ p.2.2 = 0
    rw [h.apply_symm_apply, ← hgval ⟨p, hp⟩]
    exact hGsurface ⟨p, hp⟩
  have hFband : (h ⁻¹' S) ∩ {p | p.2 ∈ Icc (-tau) tau} ⊆
      F '' (P.boundary ℝ ×ˢ (Icc (-r) r ×ˢ Icc (-r) r)) := by
    intro y hy
    have hyT : h y ∈ T := hband ⟨hy.1, by
      change |A (h y) - c| ≤ tau
      rw [hh, add_sub_cancel_left]
      exact abs_le.mpr hy.2⟩
    refine ⟨G.symm ⟨h y, hyT⟩, (G.symm ⟨h y, hyT⟩).property, ?_⟩
    change h.symm (g (G.symm ⟨h y, hyT⟩)) = y
    rw [← hgval, G.apply_symm_apply, h.symm_apply_apply]
  have hzero : (0 : ℝ) ∈ Icc (-r) r := ⟨neg_nonpos.mpr hr.le, hr.le⟩
  have hFcore (v : V) (hv : v ∈ P.boundary ℝ) : F (v, (0, 0)) = h.symm v := by
    change h.symm (g (v, (0, 0))) = h.symm v
    rw [← hgval ⟨(v, (0, 0)), hv, hzero, hzero⟩, hGcore _ rfl]
  obtain ⟨epsilon, hepsilon, K, hK, hKconvex, hdK, hcoreK,
    e, he, heheight, hestart, hecore⟩ :=
    exists_joint_cylinder_of_normalized_polygon_collar P hP hPinj hdim
      hr htau F hF hFinj hFheight hd
  have hepsr : epsilon ≤ r := (hepsilon.2.trans_le (min_le_left _ _)).le
  have hepstau : epsilon ≤ tau := (hepsilon.2.trans_le (min_le_right _ _)).le
  obtain ⟨hsection, hsmallband⟩ := joint_cylinder_whole_surface hr.le hepsr hepstau
    F hFheight hFsurface hFband (fun v hv => interior_subset (hcoreK v hv))
    e heheight hecore
  have hcores : (fun v => (F (v, (0, 0))).1) '' P.boundary ℝ =
      (fun v : V => (h.symm v).1) '' P.boundary ℝ := by
    apply image_congr
    intro v hv
    exact congrArg Prod.fst (hFcore v hv)
  refine ⟨epsilon, hepsilon, K, hK, hKconvex, hdK, ?_,
    e, he, heheight, hestart, ?_, hsmallband⟩
  · intro v hv
    simpa only [hFcore v hv] using hcoreK v hv
  · simpa only [hcores] using hsection

end PoincareConjecture.M76.ZeroChargeJoint
