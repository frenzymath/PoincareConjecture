import PoincareConjecture.Proofs.M76.PrimeReduction.ProtectedArcMove
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.General.SupportedMoveContactSet
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalSupportedNormalExtension

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)

theorem exists_original_supported_axis_ambient_move_with_support_coordinates
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
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
    (haxis_fix : ∀ x : w, (x : P2) ∈ ({a, b} : Set P2) →
      (axis x : P2) = x)
    {U : Set X} (hU : IsOpen U)
    (hzero : ∀ z ∈ D,
      T (z, 0) ∈ B.target ∧ B.symm (T (z, 0)) ∈ U)
    {Sigma : Set X} {u v : X}
    (havoid : Disjoint W ((fun z : P2 => B.symm (T (z, 0))) ⁻¹' Sigma))
    (hcontact :
      ((fun z : P2 => B.symm (T (z, 0))) '' w) ∩ Sigma =
        {u, v})
    (huv : u ≠ v) :
    ∃ (F : X ≃ₜ X) (C : Set X),
      IsCompact C ∧ C ⊆ U ∧
      (∃ r : ℝ, 0 < r ∧ C = (B.symm ∘ T) '' (D ×ˢ Icc (-r) r) ∧
        T '' (D ×ˢ Icc (-r) r) ⊆ B.target) ∧
      (∀ y ∉ C, F y = y) ∧ (∀ y ∉ U, F y = y) ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      F '' ((fun z : P2 => B.symm (T (z, 0))) '' w) =
        (fun z : P2 => B.symm (T (z, 0))) '' W ∧
      Disjoint ((fun z : P2 => B.symm (T (z, 0))) '' W) Sigma ∧
      (((fun z : P2 => B.symm (T (z, 0))) '' w) ∩
          (F.symm '' Sigma)).ncard =
        (((fun z : P2 => B.symm (T (z, 0))) '' w) ∩ Sigma).ncard - 2 := by
  let j : P2 → X := fun z => B.symm (T (z, 0))
  obtain ⟨H, hH, hmap, hqfix, hiff, havoidH⟩ :=
    exists_protected_rim_fixed_arc_move hD hw hW hab ha hb hproper
      hReplacement axis haxis haxis_fix havoid
  obtain ⟨r, hr, hTS, hcompact, hCU, F, hFzero, hFC, hFU, hFPL, hFinv⟩ :=
    exists_original_supported_normal_extension_with_support_coordinates e he B hB T hD H hH hqfix hU
      (by simpa only [j] using hzero)
  have hFimage : F '' (j '' w) = j '' W := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      have hxD : x ∈ D := hwD hx
      let xd : D := ⟨x, hxD⟩
      have hval := hFzero xd
      have hxdw : (xd : P2) ∈ w := by simpa only [xd] using hx
      have hWxd : (H xd : P2) ∈ W := (hiff xd).mp hxdw
      exact ⟨H xd, hWxd, by simpa only [j] using hval.symm⟩
    · rintro ⟨x, hxW, rfl⟩
      have hxD : x ∈ D := hWD hxW
      let xd : D := ⟨x, hxD⟩
      let x₀ : D := H.symm xd
      have hx₀w : (x₀ : P2) ∈ w := by
        apply (hiff x₀).mpr
        simpa only [x₀, xd, H.apply_symm_apply]
      have hval := hFzero x₀
      refine ⟨j (x₀ : P2), ⟨x₀, hx₀w, rfl⟩, ?_⟩
      simpa only [j, x₀, xd, H.apply_symm_apply] using hval
  have havoidX : Disjoint (j '' W) Sigma := by
    apply disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ hy
    exact disjoint_left.mp havoid hx hy
  have hfinite : (j '' w ∩ Sigma).Finite := by
    rw [hcontact]
    exact (finite_singleton _).insert _
  have hfix : EqOn F id (j '' w \ j '' w) := by
    intro x hx
    exact (hx.2 hx.1).elim
  have hedge : F '' (j '' w) = (j '' w \ j '' w) ∪ (j '' W) := by
    rw [hFimage]
    simp
  have hcontact' :
      (j '' w \ j '' w) ∩ Sigma =
        (j '' w ∩ Sigma) \ ({u, v} : Set X) := by
    rw [Set.sdiff_self, empty_inter, hcontact]
    simp
  have hu : u ∈ j '' w ∩ Sigma := by
    rw [hcontact]
    simp
  have hv : v ∈ j '' w ∩ Sigma := by
    rw [hcontact]
    simp
  have hdrop := ncard_inter_image_symm_eq_sub_two F hedge hfix havoidX
    hcontact' hfinite hu hv huv
  refine ⟨F, (B.symm ∘ T) '' (D ×ˢ Icc (-r) r), hcompact, hCU, ⟨r, hr, rfl, hTS⟩, hFC, hFU,
    hFPL, hFinv, hFimage, havoidX, ?_⟩
  simpa only [j] using hdrop

theorem exists_original_supported_axis_ambient_move
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
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
    (haxis_fix : ∀ x : w, (x : P2) ∈ ({a, b} : Set P2) →
      (axis x : P2) = x)
    {U : Set X} (hU : IsOpen U)
    (hzero : ∀ z ∈ D,
      T (z, 0) ∈ B.target ∧ B.symm (T (z, 0)) ∈ U)
    {Sigma : Set X} {u v : X}
    (havoid : Disjoint W ((fun z : P2 => B.symm (T (z, 0))) ⁻¹' Sigma))
    (hcontact :
      ((fun z : P2 => B.symm (T (z, 0))) '' w) ∩ Sigma = {u, v})
    (huv : u ≠ v) :
    ∃ (F : X ≃ₜ X) (C : Set X),
      IsCompact C ∧ C ⊆ U ∧
      (∃ r : ℝ, 0 < r ∧ C = (B.symm ∘ T) '' (D ×ˢ Icc (-r) r)) ∧
      (∀ y ∉ C, F y = y) ∧ (∀ y ∉ U, F y = y) ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      F '' ((fun z : P2 => B.symm (T (z, 0))) '' w) =
        (fun z : P2 => B.symm (T (z, 0))) '' W ∧
      Disjoint ((fun z : P2 => B.symm (T (z, 0))) '' W) Sigma ∧
      (((fun z : P2 => B.symm (T (z, 0))) '' w) ∩ (F.symm '' Sigma)).ncard =
        (((fun z : P2 => B.symm (T (z, 0))) '' w) ∩ Sigma).ncard - 2 := by
  obtain ⟨F, C, hC, hCU, ⟨r, hr, hCr, _⟩, hrest⟩ :=
    exists_original_supported_axis_ambient_move_with_support_coordinates e he B hB T
      hD hw hW hab ha hb hwD hWD hproper hReplacement axis haxis haxis_fix
      hU hzero havoid hcontact huv
  exact ⟨F, C, hC, hCU, ⟨r, hr, hCr⟩, hrest⟩

end PoincareConjecture.M76
