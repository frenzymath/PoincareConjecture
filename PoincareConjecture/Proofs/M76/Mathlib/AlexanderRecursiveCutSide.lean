import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveCollarSlab
import PoincareConjecture.Proofs.M76.Mathlib.PolygonCollarCutSide
import PoincareConjecture.Proofs.M76.Mathlib.SelectedCapNegativeSide
import PoincareConjecture.Proofs.M76.Mathlib.CollarBottomClosure










set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in



theorem AlexanderCollarSlab.exists_unit_height_direction {S : Set E}
    {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ} (M : AlexanderCollarSlab S A q β)
    {x : E} (hx : x ∈ S ∩ {z | A z = 0}) (hxq : x ≠ q) :
    ∃ v : E, A.linear v = 1 := by
  let p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
      p.2 ∈ Icc 0 (M.upper p.1)} :=
    ⟨(x, M.upper x), hx, (M.upper_bounds x hx).1, le_rfl⟩
  have hnonzero : A.linear ≠ 0 := by
    intro hz
    have h := A.linearMap_vsub (M.chart p : E) q
    change A.linear ((M.chart p : E) - q) = A (M.chart p) - A q at h
    rw [hz, LinearMap.zero_apply, M.apex_height, sub_zero, M.height] at h
    exact (M.upper_pos x hx hxq).ne' h.symm
  exact LinearMap.surjective hnonzero 1





theorem AlexanderCollarSlab.exists_selected_cut_side {S : Set E}
    {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ} (M : AlexanderCollarSlab S A q β)
    {n : ℕ} (P : Polygon E (n + 3))
    (hPe : P.HasSimplicialEdges) (hPi : Function.Injective P)
    {d s₀ s₁ : Set E} (hd : IsFinitePLBallPair (ℝ × ℝ) d (P.boundary ℝ))
    (hs₀ : IsFinitePLBallPair (ℝ × ℝ) s₀ (P.boundary ℝ))
    (hs₁ : IsFinitePLBallPair (ℝ × ℝ) s₁ (P.boundary ℝ))
    (hunion : s₀ ∪ s₁ = S) (hinter : s₀ ∩ s₁ = P.boundary ℝ)
    (hdplane : d ⊆ {x | A x = 0}) (hcap : d ∩ S = P.boundary ℝ)
    (N : SimplicialComplex ℝ E) (hN : N.faces.Finite)
    (hsection : S ∩ {x | A x = 0} = P.boundary ℝ ∪ N.space)
    (hdN : d ∩ N.space ⊆ {q}) :
    ∃ s s' : Set E, ((s = s₀ ∧ s' = s₁) ∨ (s = s₁ ∧ s' = s₀)) ∧
      IsFinitePLBallPair (ℝ × ℝ) s (P.boundary ℝ) ∧
      IsFinitePLBallPair (ℝ × ℝ) s' (P.boundary ℝ) ∧
      s ∪ s' = S ∧ s ∩ s' = P.boundary ℝ ∧
      (∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
          p.2 ∈ Icc 0 (M.upper p.1)},
        (p : E × ℝ).1 ∈ P.boundary ℝ → (M.chart p : E) ∈ s) ∧
      d ∩ closure ((s ∪ d) ∩ {x | A x < 0}) ⊆ {q} ∧
      P.boundary ℝ \ {q} ⊆ closure ((s ∪ d) ∩ {x | 0 < A x}) := by
  have hP : P.boundary ℝ ⊆ S ∩ {x | A x = 0} :=
    subset_union_left.trans hsection.symm.subset
  have hTS : M.collar ⊆ S :=
    (subset_union_left.trans M.cover.subset).trans inter_subset_left
  have hchoice := P.pointed_collar_cut_side hPe hPi M.chart M.height M.bottom hP
    M.upper_finitePL q M.apex_upper (fun x hx => M.upper_pos x (hP hx))
    hs₀ hs₁ (hTS.trans hunion.symm.subset) hinter (hP.trans inter_subset_right)
  have hchoose : ∃ s s' : Set E,
      ((s = s₀ ∧ s' = s₁) ∨ (s = s₁ ∧ s' = s₀)) ∧
      IsFinitePLBallPair (ℝ × ℝ) s (P.boundary ℝ) ∧
      IsFinitePLBallPair (ℝ × ℝ) s' (P.boundary ℝ) ∧
      s ∪ s' = S ∧ s ∩ s' = P.boundary ℝ ∧
      ∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
          p.2 ∈ Icc 0 (M.upper p.1)},
        (p : E × ℝ).1 ∈ P.boundary ℝ → (M.chart p : E) ∈ s := by
    rcases hchoice with h | h
    · exact ⟨s₀, s₁, Or.inl ⟨rfl, rfl⟩, hs₀, hs₁, hunion, hinter, fun p hp => (h p hp).1⟩
    · exact ⟨s₁, s₀, Or.inr ⟨rfl, rfl⟩, hs₁, hs₀,
        (union_comm _ _).trans hunion, (inter_comm _ _).trans hinter,
        fun p hp => (h p hp).1⟩
  obtain ⟨s, s', hlabels, hs, hs', hss, hssinter, hselected⟩ := hchoose
  have hsS : s ⊆ S := subset_union_left.trans hss.subset
  have hdmeet : d ∩ s ⊆ P.boundary ℝ :=
    (inter_subset_inter_right _ hsS).trans hcap.subset
  have hzeros : (s ∩ {x | A x = 0}) \ P.boundary ℝ ⊆ N.space := by
    rintro x ⟨hx, hxnb⟩
    exact (hsection.subset ⟨hsS hx.1, hx.2⟩).resolve_left hxnb
  obtain ⟨ec⟩ := P.nonempty_boundary_homeomorph_circle hPe hPi
  have hbconn := isConnected_sdiff_singleton_of_homeomorph_circle (P.boundary ℝ) ec q
  have hbN : P.boundary ℝ ∩ N.space ⊆ {q} := fun _ hx => hdN ⟨hd.1 hx.1, hx.2⟩
  have hside := hs.cap_negative_side_of_positive_collar M.chart M.height M.bottom hP hd.1
    A.continuous_of_finiteDimensional.continuousOn hdplane hdmeet q hbconn
    (N.isCompact_space_of_finite hN).isClosed hbN hzeros
    (fun x hx => M.upper_pos x (hP hx)) hselected
  refine ⟨s, s', hlabels, hs, hs', hss, hssinter, hselected, hside, ?_⟩
  intro x hx
  apply closure_mono (inter_subset_inter_left _ subset_union_left)
  exact M.chart.collar_bottom_mem_closure_positive M.height M.bottom (hP hx.1)
    (M.upper_pos x (hP hx.1) hx.2)
    (fun p heq _ => hselected p (heq.symm ▸ hx.1))

omit [FiniteDimensional ℝ E] in


theorem AlexanderHalfSlab.exists_unit_height_direction {S : Set E}
    {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ} (M : AlexanderHalfSlab S A q β)
    {x : E} (hx : x ∈ S ∩ {z | A z = 0}) (hxq : x ≠ q) :
    ∃ v : E, A.linear v = 1 :=
  M.toCollarSlab.exists_unit_height_direction hx hxq




theorem AlexanderHalfSlab.exists_selected_cut_side {S : Set E}
    {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ} (M : AlexanderHalfSlab S A q β)
    {n : ℕ} (P : Polygon E (n + 3))
    (hPe : P.HasSimplicialEdges) (hPi : Function.Injective P)
    {d s₀ s₁ : Set E} (hd : IsFinitePLBallPair (ℝ × ℝ) d (P.boundary ℝ))
    (hs₀ : IsFinitePLBallPair (ℝ × ℝ) s₀ (P.boundary ℝ))
    (hs₁ : IsFinitePLBallPair (ℝ × ℝ) s₁ (P.boundary ℝ))
    (hunion : s₀ ∪ s₁ = S) (hinter : s₀ ∩ s₁ = P.boundary ℝ)
    (hdplane : d ⊆ {x | A x = 0}) (hcap : d ∩ S = P.boundary ℝ)
    (N : SimplicialComplex ℝ E) (hN : N.faces.Finite)
    (hsection : S ∩ {x | A x = 0} = P.boundary ℝ ∪ N.space)
    (hdN : d ∩ N.space ⊆ {q}) :
    ∃ s s' : Set E, ((s = s₀ ∧ s' = s₁) ∨ (s = s₁ ∧ s' = s₀)) ∧
      IsFinitePLBallPair (ℝ × ℝ) s (P.boundary ℝ) ∧
      IsFinitePLBallPair (ℝ × ℝ) s' (P.boundary ℝ) ∧
      s ∪ s' = S ∧ s ∩ s' = P.boundary ℝ ∧
      (∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
          p.2 ∈ Icc 0 (M.upper p.1)},
        (p : E × ℝ).1 ∈ P.boundary ℝ → (M.chart p : E) ∈ s) ∧
      d ∩ closure ((s ∪ d) ∩ {x | A x < 0}) ⊆ {q} ∧
      P.boundary ℝ \ {q} ⊆ closure ((s ∪ d) ∩ {x | 0 < A x}) :=
  M.toCollarSlab.exists_selected_cut_side P hPe hPi hd hs₀ hs₁ hunion hinter
    hdplane hcap N hN hsection hdN

end Geometry
