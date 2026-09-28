import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Caps.TwoCircleSphere
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.TwoCapComplement









set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

local notation "V2" => (Fin 2 → ℝ)
local notation "Ann" => squareAnnulus 8 1

open Classical in


theorem exists_annulus_of_count_zero
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (hconn : IsConnected K.space) (hzero : K.surfaceEulerCount = 0)
    (L : Bool → SimplicialComplex ℝ E) (hLK : ∀ b, L b ≤ K)
    (gamma : ∀ b, sphere (0 : V2) 1 ≃ₜ (L b).space)
    (hgamma : ∀ b, (gamma b).IsFinitePL)
    (hdis : Disjoint (L false).space (L true).space)
    (hboundary : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
        if ∃ b, s ∈ (L b).faces then 1 else 2) :
    ∃ H : Ann ≃ₜ K.space, H.IsFinitePL ∧
      (∀ p : Ann, depth 8 (p : ℝ × ℝ) = -1 ↔ (H p : E) ∈ (L false).space) ∧
      (∀ p : Ann, depth 8 (p : ℝ × ℝ) = 1 ↔ (H p : E) ∈ (L true).space) := by
  classical
  obtain ⟨J, _, hJs, e, he⟩ := exists_two_circle_capped_sphere K hK hpure hlinks
    hconn hzero L hLK gamma hgamma hdis hboundary
  let d := fun b ↦ boundaryCircleCap b (L b).space
  let q := fun b ↦ (L b).space ×ˢ ({0} : Set ℝ)
  have hd (b : Bool) : IsFinitePLBallPair (ℝ × ℝ) (d b) (q b) :=
    (isFinitePLBallPair_boundaryCircleCap b (gamma b) (hgamma b)).model_equiv
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  have hdJ (b : Bool) : d b ⊆ J.space := by
    rw [hJs]
    cases b
    · exact fun _ h ↦ Or.inl (Or.inr h)
    · exact fun _ h ↦ Or.inr h
  have hcv : Convex ℝ (TriangularRoofModel.halfBall 1) := by
    rw [TriangularRoofModel.halfBall_eq_halfspaces]
    simp only [ofPred_forall]
    exact convex_iInter fun i ↦ (convex_Iic 0).affine_preimage
      (TriangularRoofModel.halfBallForms 1 i)
  obtain ⟨A, hA, hA0, hA1⟩ := exists_square_annulus_two_cap_complement e he
    (TriangularRoofModel.isCompact_halfBall (Or.inl rfl)) hcv
    (TriangularRoofModel.interior_halfBall_nonempty (Or.inl rfl))
    (by simp [Module.finrank_prod]) (hd false) (hd true) (hdJ false) (hdJ true)
    (boundaryCircleCaps_disjoint hdis)
  let Z : E →ᴬ[ℝ] E × ℝ :=
    (ContinuousAffineMap.id ℝ E).prod (ContinuousAffineMap.const ℝ E 0)
  have hqbase (b : Bool) : q b ⊆ Z '' K.space := by
    rintro x ⟨hx, hx0⟩
    exact ⟨x.1, SimplicialComplex.space_subset_of_le (hLK b) hx, Prod.ext rfl hx0.symm⟩
  have hplane (x : E × ℝ) (hx : x ∈ Z '' K.space) : x.2 = 0 := by
    obtain ⟨y, hy, rfl⟩ := hx
    rfl
  have hcarrier : J.space \ ((d false \ q false) ∪ (d true \ q true)) = Z '' K.space := by
    apply Subset.antisymm
    · intro x hx
      rcases hJs.subset hx.1 with (h | h) | h
      · exact h
      · exact hqbase false (by
          by_contra hq
          exact hx.2 (Or.inl ⟨h, hq⟩))
      · exact hqbase true (by
          by_contra hq
          exact hx.2 (Or.inr ⟨h, hq⟩))
    · intro x hx
      refine ⟨hJs.symm.subset (Or.inl (Or.inl hx)), ?_⟩
      have hq (b : Bool) (hxd : x ∈ d b) : x ∈ q b :=
        (boundaryCircleCap_plane b (L b).space).subset ⟨hxd, trivial, hplane x hx⟩
      rintro (h | h)
      · exact h.2 (hq false h.1)
      · exact h.2 (hq true h.1)
  have hZ : FinitePiecewiseAffineOn Z K.space :=
    ⟨K, hK, rfl, K.affineOnFaces_affine Z⟩
  obtain ⟨B, hB, hBval⟩ := hZ.exists_homeomorph_image
    (fun x _ y _ h ↦ congrArg Prod.fst h)
  let A' := A.trans (Homeomorph.setCongr hcarrier)
  let H := A'.trans B.symm
  have hval (p : Ann) : Z (H p) = (A p : E × ℝ) := by
    calc
      _ = (B (H p) : E × ℝ) := (hBval (H p)).symm
      _ = (A p : E × ℝ) := congrArg Subtype.val (B.apply_symm_apply (A' p))
  refine ⟨H, (hA.setCongr rfl hcarrier).trans hB.symm, ?_, ?_⟩
  · intro p
    apply (hA0 p).trans
    rw [← hval p]
    change ((H p : E) ∈ (L false).space ∧ (0 : ℝ) ∈ ({0} : Set ℝ)) ↔ _
    simp only [mem_singleton_iff, and_true]
  · intro p
    apply (hA1 p).trans
    rw [← hval p]
    change ((H p : E) ∈ (L true).space ∧ (0 : ℝ) ∈ ({0} : Set ℝ)) ↔ _
    simp only [mem_singleton_iff, and_true]

end PoincareConjecture.M76.Dehn.Annuli
