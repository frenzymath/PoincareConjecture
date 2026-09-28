import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.General.SupportedAxisAmbientMove
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.General.SupportedMoveContactSet
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteFaceCounts

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "Z" => (Set.preimage (Prod.snd : (ℝ × ℝ) → ℝ) ({0} : Set ℝ))

theorem coarse_edge_inter_prism_support_subset_axis
    {X : Type*} [TopologicalSpace X]
    (B : OpenPartialHomeomorph X V3) (T : P3 ≃ᴬ[ℝ] V3)
    {D w : Set P2} {r : ℝ} {edge : Set X}
    (hDaxis : D ∩ Z = w)
    (hprism : T '' (D ×ˢ Icc (-r) r) ⊆ B.target)
    (hedge : ∀ x ∈ edge ∩ B.source,
      (T.symm (B x)).1 ∈ Z ∧ (T.symm (B x)).2 = 0) :
    edge ∩ ((B.symm ∘ T) '' (D ×ˢ Icc (-r) r)) ⊆
      (fun z : P2 => B.symm (T (z, 0))) '' w := by
  rintro x ⟨hx, z, hz, rfl⟩
  have hzB : T z ∈ B.target := hprism ⟨z, hz, rfl⟩
  have hcoord := hedge (B.symm (T z)) ⟨hx, B.mapsTo_symm hzB⟩
  rw [B.right_inv hzB, T.symm_apply_apply] at hcoord
  refine ⟨z.1, hDaxis.subset ⟨hz.1, hcoord.1⟩, ?_⟩
  change B.symm (T (z.1, 0)) = B.symm (T z)
  rw [← hcoord.2]

theorem eqOn_coarse_edge_diff_axis_of_prism_support
    {X : Type*} [TopologicalSpace X]
    (B : OpenPartialHomeomorph X V3) (T : P3 ≃ᴬ[ℝ] V3)
    {D w : Set P2} {r : ℝ} {edge : Set X}
    (hDaxis : D ∩ Z = w)
    (hprism : T '' (D ×ˢ Icc (-r) r) ⊆ B.target)
    (hedge : ∀ x ∈ edge ∩ B.source,
      (T.symm (B x)).1 ∈ Z ∧ (T.symm (B x)).2 = 0)
    (F : X ≃ₜ X)
    (hfix : ∀ x ∉ (B.symm ∘ T) '' (D ×ˢ Icc (-r) r), F x = x) :
    EqOn F id (edge \ ((fun z : P2 => B.symm (T (z, 0))) '' w)) := by
  intro x hx
  apply hfix
  intro hxC
  exact hx.2 (coarse_edge_inter_prism_support_subset_axis B T hDaxis hprism hedge ⟨hx.1, hxC⟩)

theorem coarse_axis_image_chart_coordinates
    {X : Type*} [TopologicalSpace X]
    (B : OpenPartialHomeomorph X V3) (T : P3 ≃ᴬ[ℝ] V3)
    {s : Set P2} (hs : s ⊆ Z)
    (htarget : ∀ z ∈ s, T (z, 0) ∈ B.target) :
    ∀ x ∈ ((fun z : P2 => B.symm (T (z, 0))) '' s) ∩ B.source,
      (T.symm (B x)).1 ∈ Z ∧ (T.symm (B x)).2 = 0 := by
  rintro x ⟨⟨z, hz, rfl⟩, _⟩
  rw [B.right_inv (htarget z hz), T.symm_apply_apply]
  exact ⟨hs hz, rfl⟩

theorem exists_original_supported_full_edge_move
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (B : OpenPartialHomeomorph X V3)
    (hB : ∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3)
    (T : P3 ≃ᴬ[ℝ] V3)
    {D q w W : Set P2} {a b : P2}
    (hD : IsFinitePLBallPair P2 D q)
    (hw : IsFinitePLBallPair ℝ w {a, b})
    (hW : IsFinitePLBallPair ℝ W {a, b})
    (hab : a ≠ b) (ha : a ∈ q) (hb : b ∈ q)
    (hwD : w ⊆ D) (hWD : W ⊆ D)
    (hproper : w \ {a, b} ⊆ D \ q)
    (hReplacement : W \ {a, b} ⊆ D \ q)
    (axis : w ≃ₜ W) (haxis : axis.IsFinitePL)
    (haxis_fix : ∀ x : w, (x : P2) ∈ ({a, b} : Set P2) → (axis x : P2) = x)
    (hDaxis : D ∩ Z = w)
    {U : Set X} (hU : IsOpen U)
    (hzero : ∀ z ∈ D, T (z, 0) ∈ B.target ∧ B.symm (T (z, 0)) ∈ U)
    {Sigma edge : Set X} {u v : X}
    (havoid : Disjoint W ((fun z : P2 => B.symm (T (z, 0))) ⁻¹' Sigma))
    (hcontact : ((fun z : P2 => B.symm (T (z, 0))) '' w) ∩ Sigma = {u, v})
    (huv : u ≠ v)
    (hwedge : ((fun z : P2 => B.symm (T (z, 0))) '' w) ⊆ edge)
    (hedgeAxis : ∀ x ∈ edge ∩ B.source,
      (T.symm (B x)).1 ∈ Z ∧ (T.symm (B x)).2 = 0)
    (hfinite : (edge ∩ Sigma).Finite)
    (untouched : κ → Set X) (hprotected : ∀ i, Disjoint U (untouched i)) :
    ∃ (F : X ≃ₜ X) (C : Set X),
      IsCompact C ∧ C ⊆ U ∧
      (∃ r : ℝ, 0 < r ∧ C = (B.symm ∘ T) '' (D ×ˢ Icc (-r) r) ∧
        T '' (D ×ˢ Icc (-r) r) ⊆ B.target) ∧
      (∀ y ∉ C, F y = y) ∧ (∀ y ∉ U, F y = y) ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      EqOn F id (edge \ ((fun z : P2 => B.symm (T (z, 0))) '' w)) ∧
      F '' edge = (edge \ ((fun z : P2 => B.symm (T (z, 0))) '' w)) ∪
        ((fun z : P2 => B.symm (T (z, 0))) '' W) ∧
      edge ∩ (F.symm '' Sigma) = (edge ∩ Sigma) \ ({u, v} : Set X) ∧
      (edge ∩ (F.symm '' Sigma)).ncard = (edge ∩ Sigma).ncard - 2 ∧
      (∀ i, untouched i ∩ (F.symm '' Sigma) = untouched i ∩ Sigma) ∧
      (∀ i, (untouched i ∩ (F.symm '' Sigma)).ncard = (untouched i ∩ Sigma).ncard) := by
  let j : P2 → X := fun z => B.symm (T (z, 0))
  obtain ⟨F, C, hC, hCU, ⟨r, hr, hCr, hprism⟩, hFC, hFU, hFPL, hFinv,
      hFlocal, hdis, _⟩ :=
    exists_original_supported_axis_ambient_move_with_support_coordinates e he B hB T
      hD hw hW hab ha hb hwD hWD hproper hReplacement axis haxis haxis_fix
      hU hzero havoid hcontact huv
  have hfix : EqOn F id (edge \ j '' w) :=
    eqOn_coarse_edge_diff_axis_of_prism_support B T hDaxis hprism hedgeAxis F
      (fun x hx => hFC x (by rwa [hCr]))
  have hretimage : F '' (edge \ j '' w) = edge \ j '' w := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [hfix hy, id_eq] using hy
    · intro hx
      exact ⟨x, hx, hfix hx⟩
  have hdecomp : edge = (edge \ j '' w) ∪ (j '' w) := by
    ext x
    constructor
    · intro hx
      by_cases hxw : x ∈ j '' w
      · exact Or.inr hxw
      · exact Or.inl ⟨hx, hxw⟩
    · rintro (hx | hx)
      · exact hx.1
      · exact hwedge hx
  have hFedge : F '' edge = (edge \ j '' w) ∪ (j '' W) := by
    calc
      F '' edge = F '' ((edge \ j '' w) ∪ (j '' w)) := congrArg (image F) hdecomp
      _ = (edge \ j '' w) ∪ (j '' W) := by rw [image_union, hretimage, hFlocal]
  have hretcontact : (edge \ j '' w) ∩ Sigma = (edge ∩ Sigma) \ ({u, v} : Set X) := by
    ext x
    have hc : (x ∈ j '' w ∧ x ∈ Sigma) ↔ x ∈ ({u, v} : Set X) := by
      change x ∈ j '' w ∩ Sigma ↔ _
      rw [hcontact]
    simp only [mem_inter_iff, mem_sdiff] at *
    tauto
  have hu : u ∈ edge ∩ Sigma := by
    have h : u ∈ j '' w ∩ Sigma := by rw [hcontact]; simp
    exact ⟨hwedge h.1, h.2⟩
  have hv : v ∈ edge ∩ Sigma := by
    have h : v ∈ j '' w ∩ Sigma := by rw [hcontact]; simp
    exact ⟨hwedge h.1, h.2⟩
  have hexact : edge ∩ (F.symm '' Sigma) = (edge ∩ Sigma) \ ({u, v} : Set X) :=
    (inter_image_symm_eq_inter_diff F hFedge hfix hdis).trans hretcontact
  have hdrop := ncard_inter_image_symm_eq_sub_two F hFedge hfix hdis hretcontact hfinite hu hv huv
  have huntouched (i : κ) : EqOn F id (untouched i) := by
    intro x hx
    exact hFU x (fun hxU => disjoint_left.mp (hprotected i) hxU hx)
  exact ⟨F, C, hC, hCU, ⟨r, hr, hCr, hprism⟩, hFC, hFU, hFPL, hFinv,
    hfix, hFedge, hexact, hdrop,
    (fun i => inter_image_symm_eq_of_fixed F (huntouched i)),
    (fun i => ncard_inter_image_symm_eq_of_fixed F (huntouched i))⟩

end PoincareConjecture.M76
