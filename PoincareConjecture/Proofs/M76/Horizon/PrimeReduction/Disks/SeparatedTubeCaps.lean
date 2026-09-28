import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Disks.CircleCapAttachment
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Disks.AttachedCapNormalSigns
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Disks.ProtectedSeparatedCircleCaps
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralUnions

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
open Dehn
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

theorem exists_separated_caps_of_circle_tube
    {n : ℕ} (L : Polygon V3 (n + 3)) (hL : L.HasSimplicialEdges)
    (hLi : Function.Injective L) {D T : Set V3}
    (hD : IsFinitePLBallPair P2 D (L.boundary ℝ)) (hDT : D ⊆ T)
    (F : P2 →ᴬ[ℝ] V3) (R : V3 →ᴬ[ℝ] P2)
    (hRF : Function.LeftInverse R F) (hFR : EqOn (F ∘ R) id T)
    (M : SimplicialComplex ℝ V3) (hM : M.faces.Finite)
    (hDM : D ∩ M.space = L.boundary ℝ)
    {O : Set V3} (hO : IsOpen O) (hDO : D ⊆ O)
    {β : ℝ} (hβ : 0 < β) (sigma : C3 → V3)
    (hSigma : FinitePiecewiseAffineOn sigma (signedTubeDiamond ×ˢ Icc 0 β))
    (hSigmaO : MapsTo sigma (signedTubeDiamond ×ˢ Icc 0 β) O)
    (htriangle : ∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β,
      sigma x ∈ T ↔ x.1 ∈ signedTubeSheet 0)
    (hsphere : ∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β,
      sigma x ∈ M.space ↔ x.1 ∈ signedTubeSheet 1)
    (haxis : ∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β,
      sigma x ∈ L.boundary ℝ ↔ x.1 = (0, 0))
    (hfib : ∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β,
      ∀ y ∈ signedTubeDiamond ×ˢ Icc 0 β,
      sigma x = sigma y ↔ x.1 = y.1 ∧
        (x.2 = y.2 ∨ (x.2 = 0 ∧ y.2 = β) ∨ (y.2 = 0 ∧ x.2 = β)))
    (A : V3 →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0) (hAT : ∀ x ∈ T, A x = 0)
    (hzero : ∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β, A (sigma x) = 0 ↔ x.1.1 = 0)
    (hsides :
      ((∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β, 0 < x.1.1 → 0 < A (sigma x)) ∧
        (∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β, x.1.1 < 0 → A (sigma x) < 0)) ∨
      ((∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β, 0 < x.1.1 → A (sigma x) < 0) ∧
        (∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β, x.1.1 < 0 → 0 < A (sigma x)))) :
    ∃ caps : Bool → Set V3,
      (∀ b, IsFinitePLBallPair P2 (caps b)
        ((fun t => sigma ((if b then 1 / 4 else -1 / 4, 0), t)) '' Icc 0 β) ∧
        caps b ⊆ O ∧
        caps b ∩ M.space =
          (fun t => sigma ((if b then 1 / 4 else -1 / 4, 0), t)) '' Icc 0 β ∧
        Disjoint (caps b) T) ∧
      Disjoint (caps true) (caps false) := by
  classical
  obtain ⟨side, m, P, inner, hPi, hP, hPr, hinner, hsub, hin, hout, hraw, hinter⟩ :=
    exists_attached_circle_cap_disks L hL hLi hD hDT F R hRF hFR hβ sigma hSigma
      htriangle haxis hfib
  let raw : Bool → Set V3 := fun b => inner ∪
    (sigma ∘ taperingCapStrip β side b) '' (Icc 0 (4 * 8) ×ˢ Icc (-1) 1)
  let rim : Bool → Set V3 := fun b =>
    (fun t => sigma ((if b then 1 / 4 else -1 / 4, 0), t)) '' Icc 0 β
  have hrawBall (b : Bool) : IsFinitePLBallPair P2 (raw b) (rim b) := (hraw b).1
  have hinnerM : Disjoint inner M.space := by
    apply disjoint_left.mpr
    intro x hx hxM
    exact (hsub hx).2 (hDM.subset ⟨(hsub hx).1, hxM⟩)
  have hfib' : ∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β,
      ∀ y ∈ signedTubeDiamond ×ˢ Icc 0 β,
      sigma x = sigma y ↔ x.1 = y.1 ∧
        (x.2 = y.2 ∨ (x.2 = 0 ∧ y.2 = β) ∨ (x.2 = β ∧ y.2 = 0)) := by
    intro x hx y hy
    simpa only [and_comm] using hfib x hx y hy
  have hrawM (b : Bool) : raw b ∩ M.space = rim b :=
    attached_cap_sphere_intersection hβ sigma hSigma hfib' side hinnerM hsphere b
  have hrawO (b : Bool) : raw b ⊆ O := by
    intro x hx
    rcases (hraw b).2.2 hx with hx | hx
    · exact hDO (hsub hx).1
    · obtain ⟨y, hy, rfl⟩ := hx
      exact hSigmaO hy
  obtain ⟨B, hB, hBA, hpos, hneg, hplanar⟩ :=
    exists_attached_cap_normal_signs hβ sigma side A hA
      (fun x hx => hAT x (hDT (hsub hx).1))
      (hPr ▸ hinner.1) hzero hsides
  have hfinite (b : Bool) : ∃ K : SimplicialComplex ℝ V3,
      K.faces.Finite ∧ K.space = raw b := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hrawBall b
    exact ⟨K, hK, hKs⟩
  choose J hJ hJs using hfinite
  obtain ⟨K, hK, hKs, _⟩ := SimplicialComplex.exists_finite_triangulation_iUnion J hJ
  have hrawK (b : Bool) : raw b ⊆ K.space := by
    rw [hKs]
    exact fun _ hx => mem_iUnion.mpr ⟨b, (hJs b).symm ▸ hx⟩
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨I, hI, hIs, _⟩, _⟩, _⟩ := hinner
  have hIK : I.space ⊆ K.space := fun x hx => hrawK true (Or.inl (hIs.subset hx))
  obtain ⟨U, G, hU, hIU, hUO, hUM, hG, hdis⟩ :=
    exists_protected_separated_circle_caps I K M hI hK hM hIK
      (hIs.symm ▸ hinnerM) hO (fun x hx => hDO (hsub (hIs.subset hx)).1)
      B hB raw rim hrawBall hrawK hrawO hrawM hpos hneg
      (fun b x hx hz => hIs.symm.subset (hplanar b x hx hz))
  refine ⟨fun b => G b '' raw b, ?_, hdis⟩
  intro b
  obtain ⟨hfix, hfixM, hfixMi, hfixO, hfixrim, hball, hGO, hGM, hsign⟩ := hG b
  refine ⟨hball, hGO, hGM, disjoint_left.mpr ?_⟩
  rintro x ⟨y, hy, rfl⟩ hxT
  have hz : B (G b y) = 0 := (hBA _).mpr (hAT _ hxT)
  have hs := hsign y hy
  cases b <;> simp only [Bool.false_eq_true, if_false, if_true] at hs <;> linarith

end PoincareConjecture.M76
